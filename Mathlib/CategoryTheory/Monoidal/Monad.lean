/-
Copyright (c) 2025 Naïm Favier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naïm Favier
-/
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Strength
import Mathlib.CategoryTheory.Monoidal.Strength.Monad

/-!
# Monoidal monads

A monoidal monad `M` on a monoidal category `C` is a monad on `C` that
is also a lax monoidal functor in a compatible way.
A monoidal monad on a symmetric monoidal category is
called **symmetric** when it is braided as a lax monoidal functor.
-/

universe u₁ v₁

namespace CategoryTheory

open
  Category Functor NatTrans Monad
  MonoidalCategory BraidedCategory LaxMonoidal LaxBraided IsMonoidal
  LeftStrong RightStrong LeftStrongMonad RightStrongMonad SymmetricStrong CommutativeMonad

variable
  {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  (M : Monad C)

class MonoidalMonad extends LaxMonoidal M.toFunctor where
  [η_monoidal : IsMonoidal M.η]
  [μ_monoidal : IsMonoidal M.μ]

namespace MonoidalMonad

attribute [instance] η_monoidal μ_monoidal

@[reassoc (attr := simp)]
lemma η_tensor [MonoidalMonad M]
  : ∀ X Y : C, M.η.app (X ⊗ Y) = (M.η.app X ⊗ M.η.app Y) ≫ μ _ X Y
  := by simp [← IsMonoidal.tensor (τ := M.η)]

@[reassoc (attr := simp)]
lemma μ_tensor [MonoidalMonad M]
  : ∀ X Y : C,
    μ _ (M.obj X) (M.obj Y) ≫ M.map (μ _ X Y) ≫ M.μ.app (X ⊗ Y) = (M.μ.app X ⊗ M.μ.app Y) ≫ μ _ X Y
  := by simp [← IsMonoidal.tensor (τ := M.μ)]

@[simp]
lemma η_unit [MonoidalMonad M]
  : M.η.app (𝟙_ C) = ε _
  := by simp [← IsMonoidal.unit (τ := M.η)]

@[reassoc (attr := simp)]
lemma μ_unit [MonoidalMonad M]
  : ε _ ≫ M.map (ε _) ≫ M.μ.app (𝟙_ C) = ε _
  := by simp [← η_unit]

end MonoidalMonad

class abbrev SymmetricMonoidalMonad [SymmetricCategory C] :=
  MonoidalMonad M, LaxBraided M.toFunctor

/-!
## Monoidal monads are commutative monads

Any monoidal monad `M` can be equipped with left and right strengths making
it a strong monad in a natural way. Furthermore, this strong monad is always
commutative, because both induced lax monoidal functor structures agree
with the one we started with.
-/

open MonoidalMonad

@[simp]
instance monoidal_strong [MonoidalMonad M] : StrongMonad M where
  σ X Y := M.η.app X ▷ M.obj Y ≫ μ _ X Y
  τ X Y := M.obj X ◁ M.η.app Y ≫ μ _ X Y

  σ_natural_left f X' := by
    simp
    rw [← comp_whiskerRight_assoc]
    erw [M.η.naturality]
    rw [comp_whiskerRight_assoc, μ_natural_left]
  σ_natural_right X' f := by
    simp
    erw [whisker_exchange_assoc (M.η.app X') (M.map f) _]
    rw [μ_natural_right]
  σ_associativity X Y Z := by
    simp
    rw [← tensorHom_id, associator_naturality_assoc]
    congr 1
    rw [whisker_exchange_assoc, ← tensorHom_def'_assoc]
    simp

  τ_natural_left f X' := by
    simp
    rw [← whisker_exchange_assoc _ _ _, μ_natural_left]
  τ_natural_right X' f := by
    simp
    erw [← MonoidalCategory.whiskerLeft_comp_assoc]
    erw [M.η.naturality]
    rw [MonoidalCategory.whiskerLeft_comp_assoc, μ_natural_right]
  τ_associativity X Y Z := by
    simp
    conv_rhs => rw [← whisker_exchange_assoc, ← associator_inv_naturality_right_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← whisker_exchange, ← tensorHom_def']

  σ_η X Y := by
    simp
    rw [← tensorHom_def'_assoc]
  σ_μ X Y := by
    simp
    conv_rhs => rw [← μ_natural_left_assoc]
    rw [μ_tensor, ← tensorHom_def'_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, ← tensorHom_id, ← tensor_comp_assoc]
    simp
  τ_η X Y := by
    simp
    rw [← whisker_exchange_assoc, ← tensorHom_def'_assoc]
  τ_μ X Y := by
    simp
    conv_rhs => rw [← μ_natural_right_assoc]
    rw [μ_tensor, ← whisker_exchange_assoc, ← tensorHom_def'_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, ← id_tensorHom, ← tensor_comp_assoc]
    simp

  strengths_associativity X Y Z := by
    simp
    rw [← whisker_exchange_assoc]
    rw [associativity, associator_naturality_right_assoc, associator_naturality_left_assoc]
    rw [whisker_exchange_assoc, whisker_exchange_assoc]

lemma monoidal_left_to_right_is_tensorator [MonoidalMonad M]
  : ∀ X Y : C, left_to_right_μ' M X Y = μ M.toFunctor X Y
  := by
    intros X Y
    simp
    rw [← μ_natural_left_assoc, μ_tensor, ← tensorHom_def'_assoc, ← tensor_comp_assoc]
    simp

lemma monoidal_right_to_left_is_tensorator [MonoidalMonad M]
  : ∀ X Y : C, right_to_left_μ' M X Y = μ M.toFunctor X Y
  := by
    intros X Y
    simp
    rw [← μ_natural_right_assoc, μ_tensor, ← whisker_exchange_assoc,
      ← tensorHom_def'_assoc, ← tensor_comp_assoc]
    simp

instance monoidal_commutative [MonoidalMonad M] : CommutativeMonad M where
  strengths_commute := by
    ext X Y
    trans μ M.toFunctor X Y
    · rw [monoidal_left_to_right_is_tensorator]
    · rw [monoidal_right_to_left_is_tensorator]

/-!
Conversely, every commutative monad induces a monoidal monad, where the
commutativity of the strengths is used to prove that the monad multiplication
is a monoidal natural transformation.

Thus monoidal monads and commutative monads are equivalent, as structures on
a given monad.
-/

instance commutative_lax_monoidal_η [CommutativeMonad M] : IsMonoidal M.η where
  tensor X Y := by
    simp [LaxMonoidal.μ, μ']
    rw [tensorHom_def'_assoc, τ_η_assoc, ← M.η.naturality_assoc]
    simp

instance commutative_lax_monoidal_μ [CommutativeMonad M] : IsMonoidal M.μ where
  tensor X Y := by
    simp [LaxMonoidal.μ, μ']
    rw [M.assoc]
    slice_lhs 5 6 => erw [M.μ.naturality]
    simp
    slice_lhs 3 4 => erw [← M.μ.naturality]
    simp
    conv_lhs => rw [← reassoc_of% M.assoc]
    rw [← M.map_comp_assoc, ← M.map_comp_assoc, Category.assoc]
    rw [← right_to_left_μ', ← strengths_commute]
    simp
    conv_lhs => rw [reassoc_of% M.assoc]
    conv_lhs => rw [← M.μ.naturality_assoc]
    simp
    conv_lhs => rw [← M.assoc]
    slice_lhs 3 4 => erw [M.μ.naturality]
    slice_lhs 4 6 => rw [← M.map_comp, ← M.map_comp, ← σ_μ]
    rw [← τ_μ_assoc, M.map_comp_assoc, ← τ_natural_right_assoc,
      ← whisker_exchange_assoc, tensorHom_def']
    simp

  unit := by
    simp [LaxMonoidal.ε, ε']

@[simp]
instance commutative_monoidal [CommutativeMonad M] : MonoidalMonad M where

/-!
## Symmetric monoidal monads are symmetric commutative monads

If furthermore `C` is a symmetric monoidal category, then
the notions of symmetric monoidal monad and symmetric strong monad are equivalent.
-/

variable [SymmetricCategory C]

instance symmetric_monoidal_commutative [SymmetricMonoidalMonad M] : SymmetricStrongMonad M where
  strengths_symmetric X Y := by
    simp
    rw [← braiding_naturality_left_assoc, ← braided]

instance symmetric_commutative_monoidal [SymmetricCommutativeMonad M]
  : SymmetricMonoidalMonad M where
  braided X Y := by
    simp only [LaxMonoidal.μ, μ']
    conv_rhs => rw [strengths_commute]
    simp
    rw [← M.μ.naturality]
    simp
    conv_rhs => rw [← M.map_comp_assoc, strengths_symmetric, M.map_comp_assoc]

end CategoryTheory
