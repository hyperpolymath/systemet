-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L1.Hsub
/-!
# L1 conversion (ET-2: the one primitive relation)

The declarative judgement `DefEq` — β plus equivalence plus congruence —
and the embedding of normal forms back into terms.

Proven here: **stability** (`nf_emb : nf (embNf n) = n`) — normal forms are
fixed points of the normalizer, so `nf` is a retraction of `embNf`.

Stated-but-OPEN (milestone 2 of MECH-1, tracked in
docs/status/PROOF-STATUS.adoc — deliberately *not* stubbed here, per the
no-silent-skip constraint):

* soundness — `DefEq t (embNf (nf t))`;
* completeness — `DefEq t u → nf t = nf u`;
* their corollary `defEq_iff_nf : DefEq t u ↔ nf t = nf u`, which with
  decidable equality of `Nf` yields `decDefEq` and closes ET-2 for this
  calculus. Both rest on the substitution-commutation lemma
  `DefEq (substTy (embNf t) x (embNf u)) (embNf (substNf t x u))`, by the
  same lexicographic induction as `substNf`.
-/

namespace Systemet.L1

/-- Declarative β-conversion: the least congruent equivalence containing β.
    This is L1's one primitive relation — "equality is conversion". -/
inductive DefEq : {Γ : Ctx} → {k : Kind} → Ty Γ k → Ty Γ k → Prop where
  | refl      : DefEq t t
  | symm      : DefEq t u → DefEq u t
  | trans     : DefEq t u → DefEq u v → DefEq t v
  | beta      : (b : Ty (k₁ :: Γ) k₂) → (u : Ty Γ k₁) →
                DefEq (.app (.lam b) u) (subst0 b u)
  | arrowCong : DefEq a a' → DefEq b b' → DefEq (.arrow a b) (.arrow a' b')
  | lamCong   : DefEq b b' → DefEq (.lam b) (.lam b')
  | appCong   : DefEq f f' → DefEq a a' → DefEq (.app f a) (.app f' a')

mutual
  /-- Embed a normal form back into raw terms. -/
  def embNf : {Γ : Ctx} → {k : Kind} → Nf Γ k → Ty Γ k
    | _, _, .lam b     => .lam (embNf b)
    | _, _, .base n    => .base n
    | _, _, .arrow a b => .arrow (embNf a) (embNf b)
    | _, _, .ne x sp   => embSp (.var x) sp
  termination_by _ _ t => nfSize t
  decreasing_by all_goals (simp only [nfSize]; first | exact Nat.lt_succ_self _ | omega)

  /-- Embed a spine, folding applications around a head term. -/
  def embSp : {Γ : Ctx} → {a j : Kind} → Ty Γ a → Sp Γ a j → Ty Γ j
    | _, _, _, t, .nil       => t
    | _, _, _, t, .cons sp v => .app (embSp t sp) (embNf v)
  termination_by _ _ _ _ sp => spSize sp
  decreasing_by all_goals (simp only [spSize]; omega)
end

mutual
  /-- **Stability**: normal forms are fixed points of the normalizer. With
      `nf` total this makes `nf` a retraction of `embNf` — every normal form
      is reachable, and re-normalizing is the identity on the image. -/
  theorem nf_emb : {Γ : Ctx} → {k : Kind} → (n : Nf Γ k) → nf (embNf n) = n
    | _, _, .lam b     => by simp [embNf, nf, nf_emb b]
    | _, _, .base _    => by simp [embNf, nf]
    | _, _, .arrow a b => by simp [embNf, nf, nf_emb a, nf_emb b]
    | _, _, .ne x sp   => by rw [embNf]; exact nf_embSp x sp
  termination_by _ _ n => nfSize n
  decreasing_by all_goals (simp only [nfSize]; first | exact Nat.lt_succ_self _ | omega)

  /-- Spine form of `nf_emb`: normalizing a variable applied through an
      embedded spine recovers the neutral. -/
  theorem nf_embSp : {Γ : Ctx} → {a j : Kind} → (x : Var Γ a) → (sp : Sp Γ a j) →
      nf (embSp (.var x) sp) = .ne x sp
    | _, _, _, _, .nil       => by simp [embSp, nf]
    | _, _, _, x, .cons sp v => by
      simp [embSp, nf, nf_embSp x sp, nf_emb v, napp]
  termination_by _ _ _ _ sp => spSize sp
  decreasing_by all_goals (simp only [spSize]; omega)
end

end Systemet.L1
