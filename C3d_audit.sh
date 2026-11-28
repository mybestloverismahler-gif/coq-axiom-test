#!/usr/bin/env bash
set -euo pipefail
root=$(git rev-parse --show-toplevel)
cd "$root"
if ! command -v coqc >/dev/null || ! command -v coqchk >/dev/null; then
  eval "$(opam env)"
fi
command -v coqc; command -v coqchk
out=$(mktemp -d "$root/C3d_audit_20261128.XXXXXX")
cd "$out"
git rev-parse HEAD > HEAD.txt
coqc --version > version.log
cat > dependency.v <<'COQ'
Require Import GeoCoq.Main.Tarski_dev.Ch14_prod.
Require Import Coq.Logic.Eqdep_dec.
About sum_uniqueness.
Print Assumptions sum_uniqueness.
About prod_uniqueness.
Print Assumptions prod_uniqueness.
Print Tarski_neutral_dimensionless_with_decidable_point_equality.
Section Test.
Context `{Tn : Tarski_neutral_dimensionless}.
Context `{Td : @Tarski_neutral_dimensionless_with_decidable_point_equality Tn}.
Context `{TE : @Tarski_euclidean Tn Td}.
Lemma substitution_only : forall (X W : Tpoint) (P : Tpoint -> Prop), X = W -> P W -> P X.
Proof. intros X W P H HP. subst W. exact HP. Qed.
Print Assumptions substitution_only.
Lemma composition_no_T2 : forall O E E' A B C X Y Z,
 Sum O E E' A B X -> Prod O E E' X C Y ->
 (exists W, Sum O E E' A B W /\ Prod O E E' W C Z) -> Y = Z.
Proof.
 intros O E E' A B C X Y Z HS HP [W [HW HZ]].
 assert (X = W) as H by (eapply sum_uniqueness; eassumption).
 subst W. eapply prod_uniqueness; eassumption.
Qed.
End Test.
Check composition_no_T2.
Print Assumptions composition_no_T2.
COQ
status=0
coqc dependency.v > compile.log 2>&1 || status=$?
printf 'coqc_exit=%s\n' "$status" > status.txt
if [ "$status" = 0 ]; then
 check=0; coqchk dependency > check.log 2>&1 || check=$?
 printf 'coqchk_exit=%s\n' "$check" >> status.txt
else
 printf 'coqchk=NOT_RUN\n' >> status.txt
fi
cat compile.log status.txt
if [ -f check.log ]; then tail -5 check.log; fi
find . -maxdepth 1 -type f ! -name manifest.sha256 -print0 | sort -z | xargs -0 sha256sum > manifest.sha256
sha256sum -c manifest.sha256
cd "$root"
zip -qr "$out.zip" "$(basename "$out")"
unzip -tq "$out.zip"
sha256sum "$out.zip"
printf 'DOWNLOAD: %s\n' "$out.zip"
