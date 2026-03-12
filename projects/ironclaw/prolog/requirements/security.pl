%% security.pl — Top-level security taxonomy for ironclaw verification
%%
%% This file defines the threat model, severity ordering, and security
%% invariants used across all safety module verification.

:- module(security, [
    threat_category/1,
    severity/1,
    severity_value/2,
    severity_gte/2,
    attack_vector/1,
    invariant/2
]).

%% Threat categories corresponding to ironclaw's defense layers
threat_category(prompt_injection).
threat_category(secret_exfiltration).
threat_category(policy_violation).
threat_category(input_manipulation).
threat_category(credential_exposure).

%% Severity levels (matching ironclaw's Severity enum)
severity(low).
severity(medium).
severity(high).
severity(critical).

%% Numeric values for ordering (matching Severity::value())
severity_value(low, 1).
severity_value(medium, 2).
severity_value(high, 3).
severity_value(critical, 4).

%% Severity comparison
severity_gte(S1, S2) :-
    severity_value(S1, V1),
    severity_value(S2, V2),
    V1 >= V2.

%% Known attack vectors that must have detection patterns
attack_vector(instruction_override).
attack_vector(role_manipulation).
attack_vector(role_marker_injection).
attack_vector(special_token_injection).
attack_vector(instruction_update).
attack_vector(code_block_injection).
attack_vector(encoded_payload).
attack_vector(code_evaluation).
attack_vector(null_byte_injection).

%% Security invariants
invariant(critical_always_escaped,
    "All critical severity findings must result in content modification").

invariant(role_markers_always_detected,
    "Role markers (system:, assistant:, user:) must always be detected").

invariant(special_tokens_always_detected,
    "Special tokens (<|, |>, [INST], [/INST]) must always be detected").

invariant(case_insensitive_detection,
    "All string pattern detection must be case-insensitive").

invariant(no_false_modification,
    "Content without any pattern matches must not be modified").
