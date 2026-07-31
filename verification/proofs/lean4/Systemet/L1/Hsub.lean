-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L1.Normal
/-!
# L1 hereditary substitution and the normalizer (ET-1 evidence)

Substitution on β-normal forms that re-normalizes on the fly, after
Keller–Altenkirch. Totality is by a `(kindSize, tag, size)` lexicographic
measure — this **is** the Totality Gate for the L1 type-level calculus,
discharged by construction rather than by a separate strong-normalization
proof:

* substituting under a binder or into a spine keeps the substitution kind
  and shrinks the term (`(k, 1, size)` third component);
* hitting the substituted head variable hands off to the spine fold at the
  same kind but a smaller tag (`(k, 0, _)`);
* the spine fold β-reduces through a λ only at a *strictly smaller* kind —
  `spKindLe` bounds the intermediate arrow kind by the spine's head kind,
  so the argument kind drops the first component.

`nf` then normalizes every `Ty` by one structural pass; all β-work happens
inside the total `appSp`/`napp`.
-/

namespace Systemet.L1

mutual
  /-- Hereditary substitution on normal forms. -/
  def substNf : {Γ : Ctx} → {j : Kind} → Nf Γ j → (x : Var Γ k) → Nf (rem x) k → Nf (rem x) j
    | _, _, .lam b,     x, u => .lam (substNf b (.vs x) (wkNf .vz u))
    | _, _, .base n,    _, _ => .base n
    | _, _, .arrow a b, x, u => .arrow (substNf a x u) (substNf b x u)
    | _, _, .ne y sp,   x, u =>
      match eqv x y with
      | .same      => appSp u (substSp sp x u)
      | .diff _ y' => .ne y' (substSp sp x u)
  termination_by _ _ t _ _ => (kindSize k, 1, nfSize t)
  decreasing_by
    all_goals simp only [nfSize]
    all_goals first
      | (apply Prod.Lex.right; apply Prod.Lex.right; omega)
      | (apply Prod.Lex.right; apply Prod.Lex.left; omega)
      | (apply Prod.Lex.left
         have h := spKindLe sp
         simp only [kindSize] at h ⊢
         omega)

  /-- Hereditary substitution on spines. -/
  def substSp : {Γ : Ctx} → {a j : Kind} → Sp Γ a j → (x : Var Γ k) → Nf (rem x) k → Sp (rem x) a j
    | _, _, _, .nil,       _, _ => .nil
    | _, _, _, .cons sp v, x, u => .cons (substSp sp x u) (substNf v x u)
  termination_by _ _ _ sp _ _ => (kindSize k, 1, spSize sp)
  decreasing_by
    all_goals simp only [spSize]
    all_goals first
      | (apply Prod.Lex.right; apply Prod.Lex.right; omega)
      | (apply Prod.Lex.right; apply Prod.Lex.left; omega)

  /-- Fold a normal form through a spine, β-reducing at each step. -/
  def appSp : {Γ : Ctx} → {a j : Kind} → Nf Γ a → Sp Γ a j → Nf Γ j
    | _, _, _, u, .nil => u
    | _, _, _, u, .cons sp v =>
      match appSp u sp with
      | .lam t    => substNf t .vz v
      | .ne y sp' => .ne y (.cons sp' v)
  termination_by _ a _ _ sp => (kindSize a, 0, spSize sp)
  decreasing_by
    all_goals simp only [spSize]
    all_goals first
      | (apply Prod.Lex.right; apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left
         have h := spKindLe sp
         simp only [kindSize] at h ⊢
         omega)
end

/-- Single β-application of normal forms. -/
def napp : Nf Γ (.arr a b) → Nf Γ a → Nf Γ b
  | .lam t,   v => substNf t .vz v
  | .ne y sp, v => .ne y (.cons sp v)

/-- The normalizer: every type-level term has a β-normal form, by a
    structurally-recursive pass over the term (all β-work is inside the
    total `napp`). -/
def nf : {Γ : Ctx} → {k : Kind} → Ty Γ k → Nf Γ k
  | _, _, .var x     => .ne x .nil
  | _, _, .base n    => .base n
  | _, _, .arrow a b => .arrow (nf a) (nf b)
  | _, _, .lam b     => .lam (nf b)
  | _, _, .app f a   => napp (nf f) (nf a)
termination_by structural _ _ t => t

end Systemet.L1
