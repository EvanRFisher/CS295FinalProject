open import Data.Rational renaming (_-_ to _-ℚ_)
open import Data.Nat renaming (_>_ to _>ᴺ_ ) renaming (_≤_ to _≤ᴺ_ ) renaming (suc to Sᴺ) renaming (_*_ to _*ᴺ_) renaming (_+_ to _+ᴺ_)
open import Data.Integer renaming (_*_ to _*ᶻ_)  renaming (suc to Sᶻ)
open import Relation.Nullary
open import Data.Product
open import Agda.Builtin.Equality

--Equality from class
-- infix 8 _≡_
-- data _≡_ {A : Set} (x : A) : A → Set where
--   instance
--     ↯ : x ≡ x
-- {-# BUILTIN EQUALITY _≡_ #-}




--
--
-- Real numbers are represented by cauchy sequences
-- And are thus a pair of a function f: ℕ → ℚ
-- And a proof that ∀(ε : ℚ). ∃ (n : ℕ). ∀(a,b : ℕ).
--                             a>n ∧ b>n → | f(a) - f(b) | < ε

infix 5 _∨_
data _∨_ (A B : Set) : Set where --From IC12
  Inl : A → A ∨ B
  Inr : B → A ∨ B

--Combines - and abs
diff : ℚ → ℚ → ℚ
diff x y with x Data.Rational.≤? y
diff x y | yes (*≤* x≤y) = y -ℚ x
diff x y | no ¬p = x -ℚ y

-- diff>0 : ∀ (x y : ℚ) → diff x y  0

data ℝ : Set where
 --⟨sequence,epsilon to number,proof⟩
    ⟨_,_,_⟩ : (f   : ( ℕ → ℚ )) →
              (ε→n : (ℚ → ℕ )) →
              (∀(ε : ℚ) → ∀(a b : ℕ)
                → ε >
                → a >ᴺ (ε→n ε)
                → b >ᴺ (ε→n ε)
                → diff (f a) (f b) Data.Rational.≤ ε ) → ℝ

const : (x : ℚ) → (ℕ → ℚ) --Creates a constant function
const x = λ _ → x

const-inv : ∀ (x : ℚ) → ∀ (n : ℕ) → const x n ≡ x
const-inv = λ x n → refl

-- 0ᵣ : ℝ
-- 0ᵣ = ⟨ const (+ 0 / 1), (λ x → 0) , (λ ε a b a>e→n b>e→n → let d = diff (const (normalize 0 1) a) (const (normalize 0 1) b)
--                                                                in {!   !}) ⟩
