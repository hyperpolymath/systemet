-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L1.Completeness
/-!
# L1 decidability of conversion (ET-2)

Hand-rolled decidable equality for the mutual pair `Nf`/`Sp` — `deriving
DecidableEq` cannot handle the mutual inductives, and `.ne`/`.cons` hide a
head/argument kind that must be compared first (with `Kind`'s decidable
equality) before the pieces can be compared componentwise. With
`defEq_iff_nf` this closes ET-2: `decDefEq` decides conversion by
normalize-then-compare.
-/

namespace Systemet.L1

mutual
  /-- Decidable equality on normal forms. -/
  def decEqNf : {Γ : Ctx} → {k : Kind} → (m n : Nf Γ k) → Decidable (m = n)
    | _, _, .lam b₁, .lam b₂ =>
      match decEqNf b₁ b₂ with
      | .isTrue h => .isTrue (by rw [h])
      | .isFalse h => .isFalse fun e => h (by injection e)
    | _, _, .lam _, .ne _ _ => .isFalse fun e => by injection e
    | _, _, .ne _ _, .lam _ => .isFalse fun e => by injection e
    | _, _, .base n₁, .base n₂ =>
      match Nat.decEq n₁ n₂ with
      | .isTrue h => .isTrue (by rw [h])
      | .isFalse h => .isFalse fun e => h (by injection e)
    | _, _, .base _, .arrow _ _ => .isFalse fun e => by injection e
    | _, _, .base _, .ne _ _ => .isFalse fun e => by injection e
    | _, _, .arrow _ _, .base _ => .isFalse fun e => by injection e
    | _, _, .arrow a₁ b₁, .arrow a₂ b₂ =>
      match decEqNf a₁ a₂ with
      | .isFalse h₁ => .isFalse fun e => h₁ (by injection e)
      | .isTrue h₁ =>
        match decEqNf b₁ b₂ with
        | .isTrue h₂ => .isTrue (by rw [h₁, h₂])
        | .isFalse h₂ => .isFalse fun e => h₂ (by injection e)
    | _, _, .arrow _ _, .ne _ _ => .isFalse fun e => by injection e
    | _, _, .ne _ _, .base _ => .isFalse fun e => by injection e
    | _, _, .ne _ _, .arrow _ _ => .isFalse fun e => by injection e
    | _, _, .ne (k := c₁) y₁ sp₁, .ne (k := c₂) y₂ sp₂ =>
      if hc : c₁ = c₂ then by
        subst hc
        exact
          if hy : y₁ = y₂ then
            match decEqSp sp₁ sp₂ with
            | .isTrue hs => .isTrue (by rw [hy, hs])
            | .isFalse hs => .isFalse fun e => hs (by injection e)
          else .isFalse fun e => hy (by injection e)
      else .isFalse fun e => hc (by injection e)
  termination_by _ _ m _ => nfSize m
  decreasing_by all_goals (simp only [nfSize]; omega)

  /-- Decidable equality on spines. -/
  def decEqSp : {Γ : Ctx} → {a j : Kind} → (s t : Sp Γ a j) → Decidable (s = t)
    | _, _, _, .nil, .nil => .isTrue rfl
    | _, _, _, .nil, .cons _ _ => .isFalse fun e => by injection e
    | _, _, _, .cons _ _, .nil => .isFalse fun e => by injection e
    | _, _, _, .cons (b := b₁) sp₁ v₁, .cons (b := b₂) sp₂ v₂ =>
      if hb : b₁ = b₂ then by
        subst hb
        exact
          match decEqSp sp₁ sp₂ with
          | .isFalse h₁ => .isFalse fun e => h₁ (by injection e)
          | .isTrue h₁ =>
            match decEqNf v₁ v₂ with
            | .isTrue h₂ => .isTrue (by rw [h₁, h₂])
            | .isFalse h₂ => .isFalse fun e => h₂ (by injection e)
      else .isFalse fun e => hb (by injection e)
  termination_by _ _ _ s _ => spSize s
  decreasing_by all_goals (simp only [spSize]; omega)
end

instance : DecidableEq (Nf Γ k) := decEqNf

instance : DecidableEq (Sp Γ a j) := decEqSp

/-- **ET-2, closure**: conversion is decidable — normalize and compare. -/
def decDefEq (t u : Ty Γ k) : Decidable (DefEq t u) :=
  match decEqNf (nf t) (nf u) with
  | .isTrue h => .isTrue (defEq_iff_nf.mpr h)
  | .isFalse h => .isFalse fun d => h (defEq_iff_nf.mp d)

instance : Decidable (DefEq t u) := decDefEq t u

end Systemet.L1
