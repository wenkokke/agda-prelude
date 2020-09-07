------------------------------------------------------------------------
-- An Agda Prelude
--
-- Re-exports definitions from the standard library in a consistent way.
--
-- Re-exports Algebra, the Monad hierarchy, and some definitions from
-- Function.
--
-- For datatypes:
--   - Exports all definitions from Data.<Name> and
--     Data.<Name>.Properties in Prelude.<Name>.
--   - Exports type name and constructors.
--   - Exports Data.<Name>.Instances when unique, otherwise exports
--     quanlified versions, e.g., Product.Left.monad.
-- Occasionally exports a few more operations where these are unlikely
-- to cause name clashes.
--
-- Not to be confused with Ulf Norell's agda-prelude.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


module Prelude where


-- * Algebra

open import Algebra public


-- * Categorical

open import Category.Applicative public
  using (RawApplicative; RawApplicativeZero; RawAlternative)
open import Category.Applicative.Indexed public
  using (RawIApplicative; RawIApplicativeZero; RawIAlternative)
open import Category.Functor public
  using (RawFunctor)
open import Category.Monad public
  using (RawMonad; RawMonadZero; RawMonadPlus)
open import Category.Monad.Indexed public
  using (RawIMonad; RawIMonadZero; RawIMonadPlus)


-- * Types

module Bool where
  open import Data.Bool.Base public
  open import Data.Bool.Properties public
open Bool public hiding (module Bool)
  using (Bool; false; true; not; _∧_; _∨_; if_then_else_)

module Char where
  open import Data.Char.Base public
  open import Data.Char.Properties public
open Char public
  using (Char)

module Empty where
  open import Data.Empty public
open Empty public using (⊥; ⊥-elim)

module Fin where
  open import Data.Fin.Base public
  open import Data.Fin.Properties public
open Fin public hiding (module Fin)
  using (Fin; suc; zero)

module Float where
  open import Data.Float.Base public
  open import Data.Float.Properties public
open Float public
  using (Float)

module Integer where
  open import Data.Integer public
  open import Data.Integer.Properties public
open Integer public
  using (ℤ; +_; -[1+_])

module List where
  open import Data.List.Base public
  open import Data.List.Properties public
  open import Data.List.Categorical public
open List public hiding (module List)
  using (List; _∷_; [])
open import Data.List.Instances public

module Maybe where
  open import Data.Maybe.Base public
  open import Data.Maybe.Properties public
open Maybe hiding (module Maybe)
  using (Maybe; just; nothing)
open import Data.Maybe.Instances public

module Nat where
  open import Agda.Builtin.FromNat public
  open import Data.Nat.Base public
  open import Data.Nat.Properties public
  open import Data.Nat.Show public
open Nat public hiding (module ℕ)
  using (Number; ℕ; suc; zero)

module Product where
  open import Data.Product public
  open import Data.Product.Properties public
  module Left where
    open import Data.Product.Categorical.Left public
  module Right where
    open import Data.Product.Categorical.Right public
open Product public hiding (module Σ)
  using (Σ; Σ-syntax; ∃; ∃-syntax; _×_; _,_)

module String where
  open import Data.String.Base public
  open import Data.String.Properties public
open String public
  using (String)

module Sum where
  open import Data.Sum.Base public
  open import Data.Sum.Properties public
  module Left where
    open import Data.Sum.Categorical.Left public
  module Right where
    open import Data.Sum.Categorical.Right public
open Sum public hiding (module _⊎_)
  using (_⊎_; inj₁; inj₂)

module Unit where
  open import Data.Unit.Base public
  open import Data.Unit.Properties public
open Unit public hiding (module ⊤)
  using (⊤; tt)

module Vec where
  open import Data.Vec.Base public
  open import Data.Vec.Properties public
  open import Data.Vec.Categorical public
open Vec public hiding (module Vec)
  using (Vec; _∷_; [])
open import Data.Vec.Instances public


-- * Function

open import Function public
  using (id; const; _∘_; flip; _$_; case_of_)


-- * Identity

module Identity where
  open import Function.Identity.Categorical public
open import Function.Identity.Instances public


-- * Relations

module Negation where
  open import Relation.Nullary public
  open import Relation.Nullary.Negation public
open Negation public
  using (¬_)

module Dec where
  open import Relation.Nullary public
  open import Relation.Nullary.Decidable public
open Dec public hiding (module Dec)
  using (Dec; yes; no; True; False)

module PropEq where
  open import Relation.Binary.PropositionalEquality public
open PropEq public hiding (module _≡_)
  using (_≡_; refl)


-- * Reflection

module Rfl where
  open import Reflection public


-- * Literals

open import Agda.Builtin.FromNat public
open import Agda.Builtin.FromNeg public
open import Agda.Builtin.FromString public

import Data.Fin.Literals
import Data.Integer.Literals
import Data.Nat.Literals
import Data.String.Literals
import Data.List.Literals

instance
  numberFin : ∀ {n} → Number (Fin n)
  numberFin {n} = Data.Fin.Literals.number n

  numberℤ : Number ℤ
  numberℤ = Data.Integer.Literals.number

  numberℕ : Number ℕ
  numberℕ = Data.Nat.Literals.number

  negativeℤ : Negative ℤ
  negativeℤ = Data.Integer.Literals.negative

  isStringListChar : IsString (List Char)
  isStringListChar = Data.List.Literals.isString

  isStringString : IsString String
  isStringString = Data.String.Literals.isString
