//! `ArrStore`: the harness [`Store`], over fixed-capacity arrays.
//!
//! `approval-core` is generic over its store; the deployed one is the
//! contract's `LookupMap` impl, and `MemStore` is test support. Kani runs
//! the core over this store instead of `MemStore` because CBMC exhausted
//! 15 GB on `Vec` buffers of symbolic length (a clone of a 3-element
//! `MemStore`, or one `approve` step from an `Inv` state). Fixed arrays with
//! symbolic counts have no reallocation, and a clone is a fixed-size copy.
//!
//! It implements the `Store` laws exactly as `MemStore` does: principals are
//! an ordered list with "first match" lookup, insert-or-overwrite and
//! order-preserving removal; requests and the log are append-only sequences
//! read by position; `replace_request` ignores an out-of-range id. Pushing
//! past capacity panics, which the harness bounds rule out. That it refines
//! `MemStore` (and the contract's store) is ST-1/ST-3, milestone M2.

use crate::ids::{Acct, Key};
use approval_core::{ActionRequest, BlockTime, Principal, RequestId, Role, Store};

pub const CAP_P: usize = 4;
pub const CAP_R: usize = 4;

#[derive(Clone, Debug)]
pub struct ArrStore {
    pub owner: Acct,
    np: usize,
    p: [(Key, Principal<Acct>); CAP_P],
    nr: usize,
    r: [ActionRequest<Acct, Key>; CAP_R],
    nl: usize,
    l: [u64; CAP_R],
}

fn blank_p() -> (Key, Principal<Acct>) {
    (
        Key(0),
        Principal {
            account_id: Acct(0),
            role: Role::Agent,
            active_from: 0,
            pending: 0,
        },
    )
}

fn blank_r() -> ActionRequest<Acct, Key> {
    ActionRequest {
        id: 0,
        agent_account_id: Acct(0),
        agent_key: Key(0),
        action: String::new(),
        requested_at: BlockTime {
            height: 0,
            timestamp_ns: 0,
        },
        approval: None,
    }
}

impl ArrStore {
    pub fn new(owner: Acct) -> Self {
        ArrStore {
            owner,
            np: 0,
            p: [blank_p(), blank_p(), blank_p(), blank_p()],
            nr: 0,
            r: [blank_r(), blank_r(), blank_r(), blank_r()],
            nl: 0,
            l: [0; CAP_R],
        }
    }
    // Fixed-bound accessors. Harness code loops `0..CAP` and guards on the
    // count, which CBMC unrolls exactly, instead of looping over slices of
    // symbolic length.
    pub fn np(&self) -> usize {
        self.np
    }
    pub fn nr(&self) -> usize {
        self.nr
    }
    pub fn nl(&self) -> usize {
        self.nl
    }
    pub fn prin(&self, i: usize) -> &(Key, Principal<Acct>) {
        &self.p[i]
    }
    pub fn req(&self, i: usize) -> &ActionRequest<Acct, Key> {
        &self.r[i]
    }
    pub fn log(&self, j: usize) -> u64 {
        self.l[j]
    }
    pub fn principals(&self) -> &[(Key, Principal<Acct>)] {
        &self.p[..self.np]
    }
    pub fn requests(&self) -> &[ActionRequest<Acct, Key>] {
        &self.r[..self.nr]
    }
    pub fn approval_log(&self) -> &[u64] {
        &self.l[..self.nl]
    }
    pub fn push_principal_entry(&mut self, key: Key, p: Principal<Acct>) {
        assert!(self.np < CAP_P, "harness bound: principals");
        self.p[self.np] = (key, p);
        self.np += 1;
    }
    pub fn push_request_raw(&mut self, r: ActionRequest<Acct, Key>) {
        assert!(self.nr < CAP_R, "harness bound: requests");
        self.r[self.nr] = r;
        self.nr += 1;
    }
    pub fn push_log_raw(&mut self, id: u64) {
        assert!(self.nl < CAP_R, "harness bound: log");
        self.l[self.nl] = id;
        self.nl += 1;
    }
}

impl Store<Acct, Key> for ArrStore {
    fn owner(&self) -> &Acct {
        &self.owner
    }

    fn principal(&self, key: &Key) -> Option<Principal<Acct>> {
        let mut i = 0;
        while i < self.np {
            if self.p[i].0 == *key {
                return Some(self.p[i].1.clone());
            }
            i += 1;
        }
        None
    }

    fn insert_principal(&mut self, key: Key, principal: Principal<Acct>) {
        let mut i = 0;
        while i < self.np {
            if self.p[i].0 == key {
                self.p[i].1 = principal;
                return;
            }
            i += 1;
        }
        self.push_principal_entry(key, principal);
    }

    fn remove_principal(&mut self, key: &Key) -> Option<Principal<Acct>> {
        let mut i = 0;
        while i < self.np {
            if self.p[i].0 == *key {
                let out = self.p[i].1.clone();
                let mut j = i;
                while j + 1 < self.np {
                    self.p[j] = self.p[j + 1].clone();
                    j += 1;
                }
                self.np -= 1;
                return Some(out);
            }
            i += 1;
        }
        None
    }

    fn request_count(&self) -> u64 {
        self.nr as u64
    }

    fn request(&self, id: RequestId) -> Option<ActionRequest<Acct, Key>> {
        // A loop over concrete slots, not `self.r[id]`: cloning through a
        // symbolic index makes CBMC copy each `String` through a pointer
        // that may alias every slot, which exhausted memory in `h_read`.
        let mut i = 0;
        while i < CAP_R {
            if i < self.nr && id == i as u64 {
                return Some(self.r[i].clone());
            }
            i += 1;
        }
        None
    }

    fn push_request(&mut self, request: ActionRequest<Acct, Key>) {
        self.push_request_raw(request);
    }

    fn replace_request(&mut self, request: ActionRequest<Acct, Key>) {
        if request.id < self.nr as u64 {
            let i = request.id as usize;
            self.r[i] = request;
        }
    }

    fn approval_count(&self) -> u64 {
        self.nl as u64
    }

    fn approved_request_id(&self, approval_index: u64) -> Option<RequestId> {
        if approval_index < self.nl as u64 {
            Some(self.l[approval_index as usize])
        } else {
            None
        }
    }

    fn push_approval(&mut self, request_id: RequestId) {
        self.push_log_raw(request_id);
    }
}
