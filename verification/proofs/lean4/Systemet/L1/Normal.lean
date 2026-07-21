-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
import Systemet.L1.Syntax
/-!
# L1 β-normal forms (docs/theory/02-l1-equality.adoc)

Normal forms `Nf` and neutral spines `Sp`, intrinsically kinded like `Ty`.

Spines are **left-nested**: `Sp Γ a j` is a sequence of arguments taking a
head of kind `a` to kind `j`, and `cons sp v` appends the *last* argument.
This orientation makes "apply a neutral to one more argument" constant-time
(`.ne y (.cons sp v)` — no `snoc`), and makes the spine fold in hereditary
substitution structurally recursive.

`spKindLe` — the end kind of a spine is bounded by its head kind — is the
one-line invariant the hereditary-substitution termination measure leans on.
-/

namespace Systemet.L1

/-- Size of a kind — the primary component of the hereditary-substitution
    termination measure. -/
def kindSize : Kind → Nat
  | .star => 1
  | .arr a b => kindSize a + kindSize b + 1

mutual
  /-- β-normal forms. -/
  inductive Nf : Ctx → Kind → Type where
    | lam   : Nf (k₁ :: Γ) k₂ → Nf Γ (.arr k₁ k₂)
    | base  : Nat → Nf Γ .star
    | arrow : Nf Γ .star → Nf Γ .star → Nf Γ .star
    | ne    : Var Γ k → Sp Γ k j → Nf Γ j

  /-- Spines, left-nested: `cons sp v` appends the *last* argument. -/
  inductive Sp : Ctx → Kind → Kind → Type where
    | nil  : Sp Γ k k
    | cons : Sp Γ a (.arr b c) → Nf Γ b → Sp Γ a c
end

mutual
  /-- Index-independent size of a normal form (termination measure). -/
  def nfSize : {Γ : Ctx} → {k : Kind} → Nf Γ k → Nat
    | _, _, .lam b     => nfSize b + 1
    | _, _, .base _    => 1
    | _, _, .arrow a b => nfSize a + nfSize b + 1
    | _, _, .ne _ sp   => spSize sp + 1

  /-- Index-independent size of a spine (termination measure). -/
  def spSize : {Γ : Ctx} → {a j : Kind} → Sp Γ a j → Nat
    | _, _, _, .nil       => 0
    | _, _, _, .cons sp v => spSize sp + nfSize v + 1
end

/-- The end kind of a spine is no larger than its head kind. -/
theorem spKindLe : {Γ : Ctx} → {a j : Kind} → Sp Γ a j → kindSize j ≤ kindSize a
  | _, _, _, .nil => Nat.le_refl _
  | _, _, _, .cons sp _ =>
    Nat.le_trans (by simp [kindSize]; omega) (spKindLe sp)

mutual
  /-- Weakening of normal forms along one skipped slot. -/
  def wkNf : {Γ : Ctx} → (x : Var Γ k) → Nf (rem x) j → Nf Γ j
    | _, x, .lam b     => .lam (wkNf (.vs x) b)
    | _, _, .base n    => .base n
    | _, x, .arrow a b => .arrow (wkNf x a) (wkNf x b)
    | _, x, .ne y sp   => .ne (wkv x y) (wkSp x sp)
  termination_by _ _ t => nfSize t
  decreasing_by all_goals (simp only [nfSize]; first | exact Nat.lt_succ_self _ | omega)

  /-- Weakening of spines along one skipped slot. -/
  def wkSp : {Γ : Ctx} → (x : Var Γ k) → Sp (rem x) a j → Sp Γ a j
    | _, _, .nil       => .nil
    | _, x, .cons sp v => .cons (wkSp x sp) (wkNf x v)
  termination_by _ _ sp => spSize sp
  decreasing_by all_goals (simp only [spSize]; omega)
end

end Systemet.L1
