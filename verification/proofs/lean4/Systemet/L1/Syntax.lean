-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
/-!
# L1 syntax: the type-level core calculus (docs/theory/00-notation.adoc)

Kinds, contexts, intrinsically-kinded type-level terms with de Bruijn
variables. `Ty Γ k` is the L1 language: the simply-kinded λ-calculus with a
countable family of base constants at `★` and the object-level arrow as a
constructor. Everything downstream (normal forms, hereditary substitution,
conversion) is indexed the same way, so ill-kinded terms are unrepresentable.

The `rem`/`wkv`/`EqV` toolkit is Keller–Altenkirch's ("Hereditary
Substitutions for Simple Types", MSFP 2010), ported to Lean 4. Where a
definition matches on an argument whose type mentions `rem x`, the match is
pushed into a term-level `match` (after `x`'s constructor is known) so the
index reduces before the inner patterns elaborate.
-/

namespace Systemet.L1

/-- Kinds: `★` and type-level function kinds. -/
inductive Kind : Type where
  | star : Kind
  | arr  : Kind → Kind → Kind
deriving DecidableEq, Repr

/-- Contexts are lists of kinds (de Bruijn: position = index). -/
abbrev Ctx := List Kind

/-- Typed de Bruijn variables: `Var Γ k` is a position of kind `k` in `Γ`. -/
inductive Var : Ctx → Kind → Type where
  | vz : Var (k :: Γ) k
  | vs : Var Γ k → Var (k' :: Γ) k
deriving DecidableEq

/-- Type-level terms, intrinsically kinded. -/
inductive Ty : Ctx → Kind → Type where
  | var   : Var Γ k → Ty Γ k
  | base  : Nat → Ty Γ .star
  | arrow : Ty Γ .star → Ty Γ .star → Ty Γ .star
  | lam   : Ty (k₁ :: Γ) k₂ → Ty Γ (.arr k₁ k₂)
  | app   : Ty Γ (.arr k₁ k₂) → Ty Γ k₁ → Ty Γ k₂

/-- Context minus a variable (Keller–Altenkirch `Γ - x`). -/
def rem : {Γ : Ctx} → Var Γ k → Ctx
  | _ :: Δ,  .vz   => Δ
  | k' :: _, .vs x => k' :: rem x
termination_by structural x => x

/-- Weaken a variable of `rem x` back into `Γ` (skipping `x`'s slot). -/
def wkv : {Γ : Ctx} → (x : Var Γ k) → Var (rem x) j → Var Γ j
  | _ :: _, .vz => fun y => .vs y
  | _ :: _, .vs x => fun y =>
    match y with
    | .vz => .vz
    | .vs y => .vs (wkv x y)
termination_by structural x => x

/-- Comparing two variables: either they are the same slot (same kind), or
    the second avoids the first and lives in `rem Γ x`. -/
inductive EqV : {Γ : Ctx} → Var Γ k → Var Γ j → Type where
  | same : EqV x x
  | diff : (x : Var Γ k) → (y : Var (rem x) j) → EqV x (wkv x y)

/-- Decide which case of `EqV` holds. Total by structural recursion. -/
def eqv : {Γ : Ctx} → (x : Var Γ k) → (y : Var Γ j) → EqV x y
  | k₀ :: Δ, .vz => fun y =>
    match y with
    | .vz => .same
    | .vs y => EqV.diff (Γ := k₀ :: Δ) .vz y
  | k₀ :: Δ, .vs x => fun y =>
    match y with
    | .vz => EqV.diff (Γ := k₀ :: Δ) (.vs x) .vz
    | .vs y =>
      match eqv x y with
      | .same => .same
      | .diff x y' => EqV.diff (Γ := k₀ :: Δ) (.vs x) (.vs y')
termination_by structural x => x

/-- Index-independent size of a `Ty` (the termination measure for
    weakening/substitution, whose `Ty` argument changes context index). -/
def tySize : {Γ : Ctx} → {k : Kind} → Ty Γ k → Nat
  | _, _, .var _     => 1
  | _, _, .base _    => 1
  | _, _, .arrow a b => tySize a + tySize b + 1
  | _, _, .lam b     => tySize b + 1
  | _, _, .app f a   => tySize f + tySize a + 1
termination_by structural _ _ t => t

/-- Weakening of `Ty` along one skipped slot (needed under binders). -/
def wkTy : {Γ : Ctx} → (x : Var Γ k) → Ty (rem x) j → Ty Γ j
  | _, x, .var y     => .var (wkv x y)
  | _, _, .base n    => .base n
  | _, x, .arrow a b => .arrow (wkTy x a) (wkTy x b)
  | _, x, .lam b     => .lam (wkTy (.vs x) b)
  | _, x, .app f a   => .app (wkTy x f) (wkTy x a)
termination_by _ _ t => tySize t
decreasing_by all_goals (simp only [tySize]; first | exact Nat.lt_succ_self _ | omega)

/-- Syntactic (capture-avoiding) substitution on `Ty`, for stating β.
    Substitutes slot `x` and removes it from the context. -/
def substTy : {Γ : Ctx} → Ty Γ j → (x : Var Γ k) → Ty (rem x) k → Ty (rem x) j
  | _, .var y,     x, u =>
    match eqv x y with
    | .same      => u
    | .diff _ y' => .var y'
  | _, .base n,    _, _ => .base n
  | _, .arrow a b, x, u => .arrow (substTy a x u) (substTy b x u)
  | _, .lam b,     x, u => .lam (substTy b (.vs x) (wkTy .vz u))
  | _, .app f a,   x, u => .app (substTy f x u) (substTy a x u)
termination_by _ t _ _ => tySize t
decreasing_by all_goals (simp only [tySize]; first | exact Nat.lt_succ_self _ | omega)

/-- β-substitution of the top variable: `A[a₀ := B]`.
    `rem (vz : Var (k::Γ) k) = Γ` definitionally, so this is well-typed. -/
abbrev subst0 (b : Ty (k :: Γ) j) (u : Ty Γ k) : Ty Γ j :=
  substTy b .vz u

end Systemet.L1
