-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L1.EtaNormal
/-!
# L1 hereditary substitution on η-long forms and the η-long normalizer

The Keller–Altenkirch hereditary substitution, verbatim in structure from
`Hsub.lean` but on η-long forms. Totality is by the same
`(kindSize, tag, size)` lexicographic measure. The η-restriction *shrinks*
the definition: a normal form at an arrow kind is always a `lam`, so
`nappE` and the `cons` case of `appSpE` have a single, exhaustive clause —
the neutral branch of β-application is impossible by typing.

`nfE` normalizes every `Ty` in one structural pass; variables are
η-expanded on the way in (`etaVarE`), which is exactly what makes the
result η-long. The embeddings `embNfE`/`embSpE` read η-long forms back as
terms.
-/

namespace Systemet.L1

mutual
  /-- Hereditary substitution on η-long normal forms. -/
  def substNfE : {Γ : Ctx} → {j : Kind} → NfE Γ j → (x : Var Γ k) → NfE (rem x) k → NfE (rem x) j
    | _, _, .lam b,     x, u => .lam (substNfE b (.vs x) (wkNfE .vz u))
    | _, _, .base n,    _, _ => .base n
    | _, _, .arrow a b, x, u => .arrow (substNfE a x u) (substNfE b x u)
    | _, _, .ne y sp,   x, u =>
      match eqv x y with
      | .same      => appSpE u (substSpE sp x u)
      | .diff _ y' => .ne y' (substSpE sp x u)
  termination_by _ _ t _ _ => (kindSize k, 1, nfESize t)
  decreasing_by
    all_goals simp only [nfESize]
    all_goals first
      | (apply Prod.Lex.right; apply Prod.Lex.right; omega)
      | (apply Prod.Lex.right; apply Prod.Lex.left; omega)
      | (apply Prod.Lex.left
         have h := spEKindLe sp
         simp only [kindSize] at h ⊢
         omega)

  /-- Hereditary substitution on spines of η-long forms. -/
  def substSpE : {Γ : Ctx} → {a j : Kind} → SpE Γ a j → (x : Var Γ k) → NfE (rem x) k → SpE (rem x) a j
    | _, _, _, .nil,       _, _ => .nil
    | _, _, _, .cons sp v, x, u => .cons (substSpE sp x u) (substNfE v x u)
  termination_by _ _ _ sp _ _ => (kindSize k, 1, spESize sp)
  decreasing_by
    all_goals simp only [spESize]
    all_goals first
      | (apply Prod.Lex.right; apply Prod.Lex.right; omega)
      | (apply Prod.Lex.right; apply Prod.Lex.left; omega)

  /-- Fold an η-long form through a spine, β-reducing at each step. The
      intermediate form is at an arrow kind, hence a `lam` — the single
      clause is exhaustive. -/
  def appSpE : {Γ : Ctx} → {a j : Kind} → NfE Γ a → SpE Γ a j → NfE Γ j
    | _, _, _, u, .nil => u
    | _, _, _, u, .cons sp v =>
      match appSpE u sp with
      | .lam t => substNfE t .vz v
  termination_by _ a _ _ sp => (kindSize a, 0, spESize sp)
  decreasing_by
    all_goals simp only [spESize]
    all_goals first
      | (apply Prod.Lex.right; apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left
         have h := spEKindLe sp
         simp only [kindSize] at h ⊢
         omega)
end

/-- Single β-application of η-long forms: the function is always a `lam`. -/
def nappE : NfE Γ (.arr a b) → NfE Γ a → NfE Γ b
  | .lam t, v => substNfE t .vz v

/-- The η-long normalizer: one structural pass, η-expanding variables. -/
def nfE : {Γ : Ctx} → {k : Kind} → Ty Γ k → NfE Γ k
  | _, _, .var x     => etaVarE x
  | _, _, .base n    => .base n
  | _, _, .arrow a b => .arrow (nfE a) (nfE b)
  | _, _, .lam b     => .lam (nfE b)
  | _, _, .app f a   => nappE (nfE f) (nfE a)
termination_by structural _ _ t => t

mutual
  /-- Embed an η-long normal form back into raw terms. -/
  def embNfE : {Γ : Ctx} → {k : Kind} → NfE Γ k → Ty Γ k
    | _, _, .lam b     => .lam (embNfE b)
    | _, _, .base n    => .base n
    | _, _, .arrow a b => .arrow (embNfE a) (embNfE b)
    | _, _, .ne x sp   => embSpE (.var x) sp
  termination_by _ _ t => nfESize t
  decreasing_by all_goals (simp only [nfESize]; first | exact Nat.lt_succ_self _ | omega)

  /-- Embed a spine, folding applications around a head term. -/
  def embSpE : {Γ : Ctx} → {a j : Kind} → Ty Γ a → SpE Γ a j → Ty Γ j
    | _, _, _, t, .nil       => t
    | _, _, _, t, .cons sp v => .app (embSpE t sp) (embNfE v)
  termination_by _ _ _ _ sp => spESize sp
  decreasing_by all_goals (simp only [spESize]; omega)
end

end Systemet.L1
