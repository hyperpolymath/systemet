-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L1.EtaNormal
/-!
# L1 decidable equality of η-long normal forms

Hand-rolled decidable equality for the mutual pair `NfE`/`SpE` — as with
`Nf`/`Sp`, `deriving DecidableEq` cannot handle the mutual inductives, and
`.ne`/`.cons` hide a head/argument kind that must be compared first (with
`Kind`'s decidable equality) before the pieces can be compared
componentwise.
-/

namespace Systemet.L1

mutual
  /-- Decidable equality on η-long normal forms. -/
  def decEqNfE : {Γ : Ctx} → {k : Kind} → (m n : NfE Γ k) → Decidable (m = n)
    | _, _, .lam b₁, .lam b₂ =>
      match decEqNfE b₁ b₂ with
      | .isTrue h => .isTrue (by rw [h])
      | .isFalse h => .isFalse fun e => h (by injection e)
    | _, _, .base n₁, .base n₂ =>
      match Nat.decEq n₁ n₂ with
      | .isTrue h => .isTrue (by rw [h])
      | .isFalse h => .isFalse fun e => h (by injection e)
    | _, _, .base _, .arrow _ _ => .isFalse fun e => by injection e
    | _, _, .base _, .ne _ _ => .isFalse fun e => by injection e
    | _, _, .arrow _ _, .base _ => .isFalse fun e => by injection e
    | _, _, .arrow a₁ b₁, .arrow a₂ b₂ =>
      match decEqNfE a₁ a₂ with
      | .isFalse h₁ => .isFalse fun e => h₁ (by injection e)
      | .isTrue h₁ =>
        match decEqNfE b₁ b₂ with
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
            match decEqSpE sp₁ sp₂ with
            | .isTrue hs => .isTrue (by rw [hy, hs])
            | .isFalse hs => .isFalse fun e => hs (by injection e)
          else .isFalse fun e => hy (by injection e)
      else .isFalse fun e => hc (by injection e)
  termination_by _ _ m _ => nfESize m
  decreasing_by all_goals (simp only [nfESize]; omega)

  /-- Decidable equality on spines of η-long forms. -/
  def decEqSpE : {Γ : Ctx} → {a j : Kind} → (s t : SpE Γ a j) → Decidable (s = t)
    | _, _, _, .nil, .nil => .isTrue rfl
    | _, _, _, .nil, .cons _ _ => .isFalse fun e => by injection e
    | _, _, _, .cons _ _, .nil => .isFalse fun e => by injection e
    | _, _, _, .cons (b := b₁) sp₁ v₁, .cons (b := b₂) sp₂ v₂ =>
      if hb : b₁ = b₂ then by
        subst hb
        exact
          match decEqSpE sp₁ sp₂ with
          | .isFalse h₁ => .isFalse fun e => h₁ (by injection e)
          | .isTrue h₁ =>
            match decEqNfE v₁ v₂ with
            | .isTrue h₂ => .isTrue (by rw [h₁, h₂])
            | .isFalse h₂ => .isFalse fun e => h₂ (by injection e)
      else .isFalse fun e => hb (by injection e)
  termination_by _ _ _ s _ => spESize s
  decreasing_by all_goals (simp only [spESize]; omega)
end

instance : DecidableEq (NfE Γ k) := decEqNfE

instance : DecidableEq (SpE Γ a j) := decEqSpE

end Systemet.L1
