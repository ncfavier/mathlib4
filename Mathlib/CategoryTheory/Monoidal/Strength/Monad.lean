/-
Copyright (c) 2025 Naïm Favier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naïm Favier
-/
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Strength

/-!
# Strong monads

A tensorial strength for a monad `M` on a monoidal category `C` is
a strength for the underlying endofunctor that is compatible with the
monad operations in a certain sense.
-/

universe u₁ v₁

namespace CategoryTheory

open Category Functor Monad LeftStrong RightStrong Strong MonoidalCategory

variable
  {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  (M : Monad C)

class LeftStrongMonad extends LeftStrong M.toFunctor where
  σ_η :
    ∀ X Y : C,
      (X ◁ M.η.app Y) ≫ σ X Y = M.η.app (X ⊗ Y) := by
    aesop_cat
  σ_μ :
    ∀ X Y : C,
      (X ◁ M.μ.app Y) ≫ σ X Y = σ X (M.obj Y) ≫ M.map (σ X Y) ≫ M.μ.app (X ⊗ Y) := by
    aesop_cat

namespace LeftStrongMonad

attribute [reassoc (attr := simp)] σ_η σ_μ

end LeftStrongMonad

class RightStrongMonad extends RightStrong M.toFunctor where
  τ_η :
    ∀ X Y : C,
      (M.η.app X ▷ Y) ≫ τ X Y = M.η.app (X ⊗ Y) := by
    aesop_cat
  τ_μ :
    ∀ X Y : C,
      (M.μ.app X ▷ Y) ≫ τ X Y = τ (M.obj X) Y ≫ M.map (τ X Y) ≫ M.μ.app (X ⊗ Y) := by
    aesop_cat

namespace RightStrongMonad

attribute [reassoc (attr := simp)] τ_η τ_μ

end RightStrongMonad

class abbrev StrongMonad :=
  LeftStrongMonad M, RightStrongMonad M, Strong M.toFunctor

class abbrev SymmetricStrongMonad [SymmetricCategory C] :=
  StrongMonad M, SymmetricStrong M.toFunctor

/-!
## Strong monads are lax monoidal functors

It is common knowledge in functional programming circles that every `Monad` is an
`Applicative`. The mathematically precise version of this fact is that every strong
monad structure on `M` induces *two* lax monoidal structures on the underlying
endofunctor, corresponding to the two ways of sequencing effects (left-to-right
and right-to-left).

We say that a strong monad is **commutative** if the two induced lax monoidal
structures agree.
-/

variable [StrongMonad M]

@[simp]
abbrev left_to_right_μ' (X Y : C) : M.obj X ⊗ M.obj Y ⟶ M.obj (X ⊗ Y) :=
  τ X (M.obj Y) ≫ M.map (σ X Y) ≫ M.μ.app (X ⊗ Y)

@[simp]
abbrev right_to_left_μ' (X Y : C) : M.obj X ⊗ M.obj Y ⟶ M.obj (X ⊗ Y) :=
  σ (M.obj X) Y ≫ M.map (τ X Y) ≫ M.μ.app (X ⊗ Y)

class CommutativeMonad extends StrongMonad M where
  strengths_commute : left_to_right_μ' M = right_to_left_μ' M

class abbrev SymmetricCommutativeMonad [SymmetricCategory C] :=
  SymmetricStrongMonad M, CommutativeMonad M

open LeftStrongMonad RightStrongMonad

@[simp]
instance left_to_right : LaxMonoidal M.toFunctor where
  ε' := M.η.app (𝟙_ C)
  μ' := left_to_right_μ' M
  μ'_natural_left f X' := by
    simp
    rw [← M.map_comp_assoc, σ_natural_left, M.map_comp_assoc, ← M.μ.naturality]
    simp
  μ'_natural_right X' f := by
    simp
    rw [← M.map_comp_assoc, σ_natural_right, M.map_comp_assoc, ← M.μ.naturality]
    simp
  associativity' X Y Z := by /- This can't be idiomatic... -/
    simp
    rw [← M.μ.naturality]
    simp
    rw [← M.map_comp_assoc, ← M.map_comp_assoc]
    simp
    rw [← M.μ.naturality_assoc]
    simp
    rw [← M.map_comp_assoc, ← M.map_comp_assoc]
    simp
    congr 4
    rw [← M.μ.naturality_assoc, ← M.μ.naturality_assoc]
    simp
    rw [← M.assoc]
    repeat rw [← M.map_comp_assoc]
    simp
  left_unitality' X := by
    simp [← M.η.naturality_assoc]
  right_unitality' X := by
    simp [← M.map_comp_assoc]

end CategoryTheory
