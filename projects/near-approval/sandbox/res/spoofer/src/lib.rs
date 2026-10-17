//! RT-SPOOF (strategy.md section 5.9, VER-1): a contract that logs any line,
//! such as a byte-for-byte copy of a real `action_approved` event. Its
//! receipt succeeds, so only VER-1's `executor_id = C` rule tells the forged
//! event from a real one.

use near_sdk::{env, near};

#[near(contract_state)]
#[derive(Default)]
pub struct Spoofer {}

#[near]
impl Spoofer {
    /// Logs `line` verbatim (e.g. `EVENT_JSON:{"standard":"trust_approval",...}`).
    pub fn emit(&mut self, line: String) {
        env::log_str(&line);
    }
}
