Require Import stage57_T3_derives_check.
Require Import stage57_T3_injective_v1.

Check (fun (a : stage57_T3_derives_check.expr) =>
  stage57_T3_injective_v1.encode a).
