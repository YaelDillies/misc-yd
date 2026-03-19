# Upstreaming dashboard

The eventual goal of the MiscYD project is to not contain any significant new formalisation, but instead to act as a shallow layer over [Mathlib](https://github.com/leanprover-community/mathlib4) showing concretely how to turn paper-combinatorics into Lean-combinatorics.

As such, it is crucial to continuously upstream code from MiscYD to Mathlib. The way we organise this is with the following two lists, showing files with no MiscYD dependencies depending on whether they contain the keyword `sorry` or not.

## Files ready to upstream

The following files are `sorry`-free and do not depend on any other MiscYD, meaning they can be readily PRed to Mathlib.

{% include _upstreaming_dashboard/ready_to_upstream_snippet.md %}

{% include _upstreaming_dashboard/easy_to_unlock_snippet.md %}
