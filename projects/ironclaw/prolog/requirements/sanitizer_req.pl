%% sanitizer_req.pl — Prompt injection detection requirements
%%
%% Encodes all 27 string patterns + 4 regex patterns from ironclaw's
%% src/safety/sanitizer.rs (commit 34550add) as Prolog facts.
%%
%% Pattern format: injection_pattern(Pattern, Severity, Category)
%% Regex format:   regex_pattern(Name, Severity, Category)
%% Action format:  severity_action(Severity, Action)

:- module(sanitizer_req, [
    injection_pattern/3,
    regex_pattern/3,
    severity_action/2,
    escape_target/1,
    role_marker/1
]).

:- use_module(security).

%%% ========================================================
%%% String patterns (detected via Aho-Corasick, case-insensitive)
%%% ========================================================

%% Direct instruction injection
injection_pattern("ignore previous",     high,     instruction_override).
injection_pattern("ignore all previous", critical, instruction_override).
injection_pattern("disregard",           medium,   instruction_override).
injection_pattern("forget everything",   high,     instruction_override).

%% Role manipulation
injection_pattern("you are now",   high,   role_manipulation).
injection_pattern("act as",        medium, role_manipulation).
injection_pattern("pretend to be", medium, role_manipulation).

%% System message injection (role markers)
injection_pattern("system:",    critical, role_marker_injection).
injection_pattern("assistant:", high,     role_marker_injection).
injection_pattern("user:",      high,     role_marker_injection).

%% Special token injection
injection_pattern("<|",      critical, special_token_injection).
injection_pattern("|>",      critical, special_token_injection).
injection_pattern("[INST]",  critical, special_token_injection).
injection_pattern("[/INST]", critical, special_token_injection).

%% Instruction update attempts
injection_pattern("new instructions",     high, instruction_update).
injection_pattern("updated instructions", high, instruction_update).

%% Code/command injection markers
injection_pattern("```system",     high,   code_block_injection).
injection_pattern("```bash\nsudo", medium, code_block_injection).

%%% ========================================================
%%% Regex patterns (more complex detection)
%%% ========================================================

regex_pattern(base64_payload, medium,   encoded_payload).
regex_pattern(eval_call,      high,     code_evaluation).
regex_pattern(exec_call,      high,     code_evaluation).
regex_pattern(null_byte,      critical, null_byte_injection).

%%% ========================================================
%%% Severity-to-action mapping
%%% ========================================================

%% Only critical severity triggers content modification (escaping)
severity_action(critical, escape).
severity_action(high,     warn).
severity_action(medium,   warn).
severity_action(low,      warn).

%%% ========================================================
%%% Escape targets (what gets modified when critical is found)
%%% ========================================================

%% These are the specific strings replaced during escape_content()
escape_target("<|").
escape_target("|>").
escape_target("[INST]").
escape_target("[/INST]").
escape_target("\x00").     % null bytes are removed

%% Role markers escaped at line start
role_marker("system:").
role_marker("user:").
role_marker("assistant:").
