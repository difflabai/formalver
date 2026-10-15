//! RT-RELAY (strategy.md section 5.9): a third-party contract that forwards
//! any call to the approval contract. A key holder tricked into calling it
//! signs the transaction, but the approval contract sees this contract's
//! account as predecessor, so the core must reject with `IndirectCall`.
//!
//! RT-TRACE also deploys it on trace accounts to realise callers whose
//! predecessor differs from their signer.

use near_sdk::{near, AccountId, Gas, GasWeight, NearToken, Promise};

#[near(contract_state)]
#[derive(Default)]
pub struct Relay {}

#[near]
impl Relay {
    /// Calls `receiver.method(args)` (JSON text) with all remaining gas and
    /// returns that call's result, so the transaction fails if it fails.
    pub fn forward(&self, receiver: AccountId, method: String, args: String) -> Promise {
        Promise::new(receiver).function_call_weight(
            method,
            args.into_bytes(),
            NearToken::from_yoctonear(0),
            Gas::from_gas(0),
            GasWeight(1),
        )
    }
}
