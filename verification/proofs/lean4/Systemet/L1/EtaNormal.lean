-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L1.Normal
/-!
# L1 η-long normal forms (ET-η, extending MECH-1)

η-long normal forms `NfE` and neutral spines `SpE`, after Keller–Altenkirch
("Hereditary Substitutions for Simple Types", MSFP 2010), whose development
is natively η-long: a neutral `ne x sp` is a normal form **only at the base
kind `★`**, so every η-long form at kind `k₁ ⇒ k₂` is a `lam`.

`etaNe` is η-expansion of a neutral (a head variable applied through a
spine) by *structural recursion on the result kind*: at `★` the neutral is
already normal; at `b ⇒ c` we go under a binder, weaken the spine, append
the η-expanded fresh variable, and recurse at `c` (the fresh variable is
itself expanded at the strictly smaller kind `b`).
-/

namespace Systemet.L1

mutual
  /-- η-long β-normal forms: neutrals are admitted **only at `★`**. -/
  inductive NfE : Ctx → Kind → Type where
    | lam   : NfE (k₁ :: Γ) k₂ → NfE Γ (.arr k₁ k₂)
    | base  : Nat → NfE Γ .star
    | arrow : NfE Γ .star → NfE Γ .star → NfE Γ .star
    | ne    : Var Γ k → SpE Γ k .star → NfE Γ .star

  /-- Spines of η-long forms, left-nested (`cons sp v` appends the *last*
      argument), exactly as `Sp`. -/
  inductive SpE : Ctx → Kind → Kind → Type where
    | nil  : SpE Γ k k
    | cons : SpE Γ a (.arr b c) → NfE Γ b → SpE Γ a c
end

mutual
  /-- Index-independent size of an η-long form (termination measure). -/
  def nfESize : {Γ : Ctx} → {k : Kind} → NfE Γ k → Nat
    | _, _, .lam b     => nfESize b + 1
    | _, _, .base _    => 1
    | _, _, .arrow a b => nfESize a + nfESize b + 1
    | _, _, .ne _ sp   => spESize sp + 1

  /-- Index-independent size of a spine (termination measure). -/
  def spESize : {Γ : Ctx} → {a j : Kind} → SpE Γ a j → Nat
    | _, _, _, .nil       => 0
    | _, _, _, .cons sp v => spESize sp + nfESize v + 1
end

/-- The end kind of a spine is no larger than its head kind. -/
theorem spEKindLe : {Γ : Ctx} → {a j : Kind} → SpE Γ a j → kindSize j ≤ kindSize a
  | _, _, _, .nil => Nat.le_refl _
  | _, _, _, .cons sp _ =>
    Nat.le_trans (by simp [kindSize]; omega) (spEKindLe sp)

mutual
  /-- Weakening of η-long forms along one skipped slot. -/
  def wkNfE : {Γ : Ctx} → (x : Var Γ k) → NfE (rem x) j → NfE Γ j
    | _, x, .lam b     => .lam (wkNfE (.vs x) b)
    | _, _, .base n    => .base n
    | _, x, .arrow a b => .arrow (wkNfE x a) (wkNfE x b)
    | _, x, .ne y sp   => .ne (wkv x y) (wkSpE x sp)
  termination_by _ _ t => nfESize t
  decreasing_by all_goals (simp only [nfESize]; first | exact Nat.lt_succ_self _ | omega)

  /-- Weakening of spines along one skipped slot. -/
  def wkSpE : {Γ : Ctx} → (x : Var Γ k) → SpE (rem x) a j → SpE Γ a j
    | _, _, .nil       => .nil
    | _, x, .cons sp v => .cons (wkSpE x sp) (wkNfE x v)
  termination_by _ _ sp => spESize sp
  decreasing_by all_goals (simp only [spESize]; omega)
end

/-- η-expansion of a neutral, by structural recursion on the result kind:
    at `★` keep the neutral; at `b ⇒ c` bind a fresh variable of kind `b`,
    weaken, append the η-expanded fresh variable, and recurse at `c`. -/
def etaNe : (j : Kind) → {Γ : Ctx} → {a : Kind} → Var Γ a → SpE Γ a j → NfE Γ j
  | .star, _, _, x, sp => .ne x sp
  | .arr b c, _, _, x, sp =>
    .lam (etaNe c (.vs x) (.cons (wkSpE .vz sp) (etaNe b .vz .nil)))
termination_by structural j => j

/-- η-expansion of a variable: the η-long normal form of `.var x`. -/
abbrev etaVarE {Γ : Ctx} {a : Kind} (x : Var Γ a) : NfE Γ a := etaNe a x .nil

end Systemet.L1
