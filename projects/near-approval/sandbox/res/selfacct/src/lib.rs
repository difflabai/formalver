//! RT-SELFACCT (strategy.md section 5.9, finding F-9): code deployed on the
//! signer's *own* account that calls the approval contract. The approval
//! contract then sees predecessor = signer, so `predecessor == signer` does
//! not rule this case out: only DEP-1.4 (registered keys are function-call
//! keys whose receiver is the approval contract) and VER-8 do.

use near_sdk::{near, AccountId, Gas, GasWeight, NearToken, Promise};

#[near(contract_state)]
#[derive(Default)]
pub struct SelfAccount {}

fn forward_to(contract: AccountId, method: &str, args: String) -> Promise {
    Promise::new(contract).function_call_weight(
        method.to_string(),
        args.into_bytes(),
        NearToken::from_yoctonear(0),
        Gas::from_gas(0),
        GasWeight(1),
    )
}

#[near]
impl SelfAccount {
    /// `target.request_action(action)`, made by this account's code.
    pub fn request(&self, target: AccountId, action: String) -> Promise {
        forward_to(
            target,
            "request_action",
            near_sdk::serde_json::json!({ "action": action }).to_string(),
        )
    }

    /// `target.approve(request_id, action)`, made by this account's code.
    pub fn approve(&self, target: AccountId, request_id: u64, action: String) -> Promise {
        forward_to(
            target,
            "approve",
            near_sdk::serde_json::json!({ "request_id": request_id, "action": action })
                .to_string(),
        )
    }
}
