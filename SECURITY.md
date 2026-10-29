# Security

Report vulnerabilities privately through [GitHub Security Advisories](https://github.com/difflabai/formalver/security/advisories/new). Do not open a public issue or pull request containing an unfixed vulnerability or credentials.

Include the affected commit, the relevant workflow, script or verification claim, reproduction steps, and the security impact. Redact credentials and personal information from logs and attachments. The current `main` branch is supported; older verification snapshots may need to be reproduced on `main`.

For vulnerabilities in the trust-framework approval contract itself, follow [trust-framework's security policy](https://github.com/difflabai/trust-framework/blob/main/SECURITY.md). Report problems in formalver's CI, tooling, specifications, or proof assumptions here, including cases where a check can incorrectly report success.

Passing verification does not establish that every specification or trusted assumption is correct. Consult the [verification status](projects/near-approval/status.toml) and [documented assumptions and review requirements](projects/near-approval/strategy.md) when interpreting a result. A green CI run is not an independent specification sign-off.
