module Prelude where


-- * Types

import Data.Bool
import Data.Bool.Properties
module Bool where
  open Data.Bool public
  open Data.Bool.Properties public
open Bool public hiding (module Bool) using (Bool; false; true)

import Data.Fin
import Data.Fin.Properties
module Fin where
  open Data.Fin public
  open Data.Fin.Properties public
open Fin public hiding (module Fin) using (Fin; suc; zero)

import Data.Float
import Data.Float.Properties
module Float where
  open Data.Float public
  open Data.Float.Properties public
open Float public using (Float)

import Data.Nat
import Data.Nat.Properties
module Nat where
  open Data.Nat public
  open Data.Nat.Properties public
open Nat public hiding (module ℕ) using (ℕ; suc; zero)

import Data.List
import Data.List.Properties
module List where
  open Data.List public
  open Data.List.Properties public
open List public hiding (module List) using (List; _∷_; [])

import Data.Maybe
import Data.Maybe.Properties
module Maybe where
  open Data.Maybe public
  open Data.Maybe.Properties public
open Maybe hiding (module Maybe) using (Maybe; just; nothing)

import Data.Vec
import Data.Vec.Properties
module Vec where
  open Data.Vec public
  open Data.Vec.Properties public
open Vec public hiding (module Vec) using (Vec; _∷_; [])


-- * Relations

import Relation.Nullary
import Relation.Nullary.Decidable
module Dec where
  open Relation.Nullary public
  open Relation.Nullary.Decidable public
open Dec public hiding (module Dec) using (Dec; yes; no)

import Relation.Binary.PropositionalEquality
module PropEq where
  open Relation.Binary.PropositionalEquality public
open PropEq public hiding (module _≡_) using (_≡_; refl)
