%% threat_model.pl -- Adversaries, threats and trust assumptions (strategy section 3)
%%
%% Transcribed from strategy.md sections 3.1, 3.2 and 3.3 at pin 3426c92.
%% ASM-TLA-SCOPE is not in section 3.3; it is taken from status.toml and
%% strategy 17.3 (TLA+ bounds). Likewise ASM-LEAN-TLA (strategy 18).
%%
%%   adversary(Id, Capabilities)
%%   threat(Id, Threat, Residual)        Residual = none | Text
%%   mitigated_by(Threat, PropertyOrAssumption)
%%   accepted_risk(Subject, Text)        Subject = threat id | method(M)
%%   assumption(Id, Text, Level)         Level = high | med | low | policy | 'n/a'
%%                                       (a mixed level is recorded as its lowest component)
%%   assumption_checked_by(Asm, Check)

:- module(threat_model, [
    adversary/2,
    threat/3,
    mitigated_by/2,
    accepted_risk/2,
    assumption/3,
    assumption_checked_by/2,
    level_rank/2
]).

%%% ========================================================
%%% 3.1 Adversaries
%%% ========================================================

adversary('ADV-AG',  "Malicious or compromised agent: holds registered agent keys, picks any action of 1-2048 bytes (including control and bidi characters), calls anything any number of times, controls its own accounts and contracts.").
adversary('ADV-AP',  "Rogue approver: the same, with an approver key.").
adversary('ADV-RC',  "Malicious contract or relayer: gets a key holder to sign a transaction to it; relays meta-transactions.").
adversary('ADV-OW',  "Compromised owner: add_agent, add_approver, revoke_key.").
adversary('ADV-CA',  "Holder of a full-access key on C: can redeploy or delete the contract.").
adversary('ADV-GR',  "Griefer: unregistered caller, or a registered agent spamming requests.").
adversary('ADV-RPC', "Lying or non-final RPC: shows wrong or not-yet-final state.").

%%% ========================================================
%%% 3.2 Threats -> mitigating properties
%%% ========================================================

threat('T1',  "Approval with no genuine approver, or self-approval", "Sybil accounts registered by the owner (ASM-OWNER)").
threat('T2',  "Request attributed to another agent", none).
threat('T3',  "Action changed after request or approval", "Redeploy (T11)").
threat('T4',  "Unregistered, wrong-role or revoked key acts", none).
threat('T5',  "Approver approves content it didn't review", "UI rendering (ASM-DISPLAY)").
threat('T6',  "Double approval, or log inflation", none).
threat('T7',  "A rogue approver approves anything", "By design: TR-1 gives accountability; TR-3 stops it after revocation").
threat('T8',  "Relayed signature (phishing contract)", "none if VER-8 is applied; otherwise code on the signer's own account (F-9)").
threat('T9',  "Owner compromise", "New approvals; DoS via revocation").
threat('T10', "Revoked agent's queued requests get approved after re-registration", none).
threat('T11', "Contract redeployed, deleted or recreated", "Governance keys, if allowed").
threat('T12', "Storage exhaustion by an agent", "Approved and void requests accumulate").
threat('T13', "Unregistered callers grief the contract", none).
threat('T14', "Accepted request can never be approved (log limit)", none).
threat('T15', "Expensive views", none).
threat('T16', "Spoofed EVENT_JSON from another contract", "Verifier bugs").
threat('T17', "Event from a failed receipt", "none, if verifiers follow VER-1").
threat('T18', "Non-final or forked reads", "RPC honesty").
threat('T19', "Paging client misses proofs", none).
threat('T20', "Init hijack or re-init", none).
threat('T21', "Hidden entrypoints", none).
threat('T22', "Attached funds", "Plain transfers to C are locked forever (accepted)").
threat('T23', "Proof replayed for a second execution", "Executor bugs").

mitigated_by('T1', 'TX-5').  mitigated_by('T1', 'INV-5').  mitigated_by('T1', 'INV-6').
mitigated_by('T1', 'TR-1').  mitigated_by('T1', 'VER-4').
mitigated_by('T2', 'TX-3').  mitigated_by('T2', 'TX-4').   mitigated_by('T2', 'TR-1').
mitigated_by('T2', 'SH-1').  mitigated_by('T2', 'ASM-SIGNER'). mitigated_by('T2', 'ASM-PRED').
mitigated_by('T3', 'HIST-1'). mitigated_by('T3', 'HIST-2'). mitigated_by('T3', 'SH-12').
mitigated_by('T4', 'TX-3').  mitigated_by('T4', 'TR-3').   mitigated_by('T4', 'HIST-8').
mitigated_by('T5', 'TX-5').  mitigated_by('T5', 'TR-1').
mitigated_by('T6', 'TX-5').  mitigated_by('T6', 'INV-3').  mitigated_by('T6', 'INV-4').
mitigated_by('T6', 'TR-2').
mitigated_by('T7', 'TR-1').  mitigated_by('T7', 'TR-3').
mitigated_by('T8', 'TX-3').  mitigated_by('T8', 'RT-RELAY'). mitigated_by('T8', 'RT-FCKEY').
mitigated_by('T8', 'DEP-1'). mitigated_by('T8', 'VER-8').
mitigated_by('T9', 'HIST-6'). mitigated_by('T9', 'HIST-7'). mitigated_by('T9', 'DEP-1').
mitigated_by('T9', 'VER-4').
mitigated_by('T10', 'TR-3'). mitigated_by('T10', 'HIST-8'). mitigated_by('T10', 'INV-8').
mitigated_by('T11', 'SH-12'). mitigated_by('T11', 'DEP-1'). mitigated_by('T11', 'VER-2').
mitigated_by('T11', 'VER-3'). mitigated_by('T11', 'VER-6'). mitigated_by('T11', 'RT-CODEHASH').
mitigated_by('T11', 'RT-RESET').
mitigated_by('T12', 'INV-9'). mitigated_by('T12', 'TR-6'). mitigated_by('T12', 'RES-1').
mitigated_by('T13', 'TX-0').
mitigated_by('T14', 'RES-2').
mitigated_by('T15', 'RD-2'). mitigated_by('T15', 'ROB-4'). mitigated_by('T15', 'RES-3').
mitigated_by('T16', 'VER-1'). mitigated_by('T16', 'RT-SPOOF').
mitigated_by('T17', 'VER-1'). mitigated_by('T17', 'RT-REVERT'). mitigated_by('T17', 'RT-BATCH').
mitigated_by('T18', 'VER-1'). mitigated_by('T18', 'VER-5'). mitigated_by('T18', 'ASM-FINAL').
mitigated_by('T19', 'RD-4').
mitigated_by('T20', 'SH-9').
mitigated_by('T21', 'SH-11').
mitigated_by('T22', 'SH-10').
mitigated_by('T23', 'VER-7').

% Residuals in the 3.2 table that are accepted rather than mitigated away.
accepted_risk('T1',  "Sybil accounts registered by the owner: policy ASM-OWNER (owner is a multisig/DAO, DEP-1; verifier allowlist, VER-4).").
accepted_risk('T3',  "Redeploy is T11.").
accepted_risk('T5',  "Rendering of the action text by approver UIs: policy ASM-DISPLAY.").
accepted_risk('T7',  "A rogue approver can approve anything until revoked: by design (accountability via TR-1, stopped by TR-3).").
accepted_risk('T8',  "Code deployed on the signer's own account can forward calls unless VER-8 is applied (F-9).").
accepted_risk('T9',  "A compromised owner can register new approvers and deny service by revoking keys.").
accepted_risk('T11', "Governance keys on C, if the deployment allows them.").
accepted_risk('T12', "Approved and void requests accumulate (economics are a non-goal).").
accepted_risk('T16', "Verifier implementation bugs.").
accepted_risk('T17', "Verifiers that do not follow VER-1.").
accepted_risk('T18', "RPC honesty.").
accepted_risk('T22', "Plain transfers to C are locked forever.").
accepted_risk('T23', "Executor implementation bugs.").
% C-4: `new` sets the owner (authority-changing) and emits no event (README lists none).
% AMBIGUOUS: the text does not say whether this is an accepted gap; recorded as one,
% since init happens once, inside the DEP-1 deploy transaction, and get_owner exposes it.
accepted_risk(method(new), "Init emits no event: it runs once (SH-9), in the DEP-1 deploy transaction, and the owner is readable via get_owner.").

%%% ========================================================
%%% 3.3 Trust assumptions (TCB)
%%% ========================================================

assumption('ASM-SIGNER',  "signer_account_pk() is the key whose signature over the originating tx was verified, an access key of signer_account_id() at that time; signatures are unforgeable.", high).
assumption('ASM-PRED',    "predecessor_account_id() can't be forged; equals the signer for the tx's first receipt and when code on the signer's own account makes the call (F-9).", high).
assumption('ASM-ATOMIC',  "Atomicity is per receipt; a panic, out-of-gas or LackBalanceForState reverts every write of that receipt; logs of a failed receipt may remain visible.", med).   % high (revert); med (logs)
assumption('ASM-SEQ',     "Receipts on one account execute one at a time; no promises, no reentrancy; each successful action is one atomic model step.", high).
assumption('ASM-TIME',    "block_height and block_timestamp never decrease across receipts on one account.", med).
assumption('ASM-FINAL',   "State at finality final is never reverted.", high).
assumption('ASM-CODE',    "Code changes only through DeployContract or UseGlobalContract on C (or DeployGlobalContract for a global contract by account id); DeleteAccount erases state.", med).
assumption('ASM-SDK',     "#[init] panics if state exists; #[private] requires predecessor = current account; non-payable methods reject deposits; &self methods never write; only #[near] methods are exported; PanicOnDefault blocks default init.", high).
assumption('ASM-STORE',   "store::LookupMap is a map keyed by prefix ++ borsh(key); writes are flushed when the contract struct drops after state_write.", med).  % high (semantics); med (flush)
assumption('ASM-IDENT',   "PartialEq on AccountId and PublicKey matches Borsh-byte equality; the core uses A/K only via Clone and PartialEq (parametricity).", high).
assumption('ASM-STAKE',   "The account must hold storage_usage x 10^19 yocto, about 40 bytes overhead per record.", med).
assumption('ASM-LIMITS',  "max_total_log_length 16384 B, 100 logs, 4 MiB return data, 300 TGas per call; view gas cap per node.", med).
assumption('ASM-META',    "NEP-366: the inner receipt has signer = relayer, so relayed calls fail IndirectCall; same for NEP-518 eth-implicit accounts.", med).
assumption('ASM-FCKEY',   "Function-call keys restrict receiver and methods, can't attach a deposit, have an allowance and can't add keys.", high).
assumption('ASM-COMPILE', "rustc/LLVM/wasm-opt preserve core semantics from host to wasm32; overflow-checks stay on in release.", 'n/a').
assumption('ASM-MODEL',   "Until M5: a core step on a state larger than the Kani bound behaves like one within it (small scope).", med).
assumption('ASM-TLA-SCOPE', "TLA+ model bounds: behaviours with more requests, keys or accounts than TLC and Apalache explore add no new violations (since strategy 18, needed for liveness only).", med).
assumption('ASM-LEAN-TLA', "The Lean machine transcribes ApprovalCore.tla and ApprovalProps.tla.", high).
assumption('ASM-SPEC',    "The specs (spec.rs, Verus, Prolog) state the intended behaviour.", 'n/a').
assumption('ASM-TOOLS',   "Kani, Verus with Z3, scryer-prolog, TLC, Apalache and the Lean 4 kernel are sound at the pinned versions.", 'n/a').
assumption('ASM-OWNER',   "The owner registers keys honestly.", policy).
assumption('ASM-DEPLOY',  "The deployed code is the reproducible build of the pin, locked at deploy.", policy).
assumption('ASM-DISPLAY', "The approver UI renders action faithfully (escaped).", policy).
assumption('ASM-NU',      "The Rust (norm.rs) and Lean (Ident.lean) transcriptions of LINK's class, representative and transport functions agree (strategy 18.6.1).", high).
assumption('ASM-STRLEN',  "(M5 only) String::len is the UTF-8 byte length and is_empty <=> len = 0.", high).

assumption_checked_by('ASM-SIGNER', 'RT-KEY').
assumption_checked_by('ASM-PRED', 'RT-RELAY').
assumption_checked_by('ASM-PRED', 'RT-SELFACCT').
assumption_checked_by('ASM-ATOMIC', 'RT-REVERT').
assumption_checked_by('ASM-ATOMIC', 'RT-BATCH').
assumption_checked_by('ASM-SEQ', 'SH-12').
assumption_checked_by('ASM-CODE', 'RT-RESET').
assumption_checked_by('ASM-CODE', 'DEP-1').
assumption_checked_by('ASM-SDK', 'SH-9').
assumption_checked_by('ASM-SDK', 'SH-10').
assumption_checked_by('ASM-SDK', 'SH-11').
assumption_checked_by('ASM-STORE', 'ST-4').
assumption_checked_by('ASM-STORE', 'ST-5').
assumption_checked_by('ASM-STORE', 'ST-6').
assumption_checked_by('ASM-STAKE', 'RES-1').
assumption_checked_by('ASM-LIMITS', 'RES-2').
assumption_checked_by('ASM-LIMITS', 'RES-3').
assumption_checked_by('ASM-META', 'RT-METATX').
assumption_checked_by('ASM-FCKEY', 'RT-FCKEY').
assumption_checked_by('ASM-COMPILE', 'RT-CODEHASH').
assumption_checked_by('ASM-COMPILE', 'RT-TRACE').
assumption_checked_by('ASM-MODEL', 'MC-2').
assumption_checked_by('ASM-NU', 'LINK').
assumption_checked_by('ASM-TLA-SCOPE', 'TLA-IND').
assumption_checked_by('ASM-TLA-SCOPE', 'REF-5').
assumption_checked_by('ASM-TLA-SCOPE', 'LEAN-IND').
assumption_checked_by('ASM-LEAN-TLA', 'MC-4').
assumption_checked_by('ASM-LEAN-TLA', 'REF-5L').
assumption_checked_by('ASM-SPEC', 'C-7').
assumption_checked_by('ASM-SPEC', 'MC-2').
assumption_checked_by('ASM-OWNER', 'DEP-1').
assumption_checked_by('ASM-OWNER', 'VER-4').
assumption_checked_by('ASM-DEPLOY', 'DEP-1').
assumption_checked_by('ASM-DEPLOY', 'VER-2').
assumption_checked_by('ASM-DEPLOY', 'VER-3').

%% level_rank(Level, Rank): C-10 compares against `high`.
level_rank(high,   3).
level_rank(med,    2).
level_rank(low,    1).
level_rank(policy, 0).
level_rank('n/a',  0).
