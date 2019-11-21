open import Data.Rational
open import Data.Nat renaming (_>_ to _>ᴺ_ ) renaming (_≤_ to _≤ᴺ_ ) renaming (suc to Sᴺ) renaming (_*_ to _*ᴺ_) renaming (_+_ to _+ᴺ_)
open import Data.Nat.GCD
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Data.Integer renaming (_*_ to _*ᶻ_)  renaming (suc to Sᶻ)
open import Relation.Nullary
open import Data.Product


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

≤-suc : ∀ {m n} → m ≤ᴺ n → Sᴺ m ≤ᴺ Sᴺ n
≤-suc a = ≤′⇒≤ ( s≤′s (≤⇒≤′ a))

-- gcd0 : ∀(m n : ℕ) → (n >ᴺ 0) → proj₁ (gcd m n) >ᴺ 0
_+ℚ_ : ℚ → ℚ → ℚ
a +ℚ b = {! a b  !}
--((y↑ *ᶻ (+ Sᴺ x↓)) - (x↑ *ᶻ (+ Sᴺ y↓))) | Sᴺ (x↓ *ᴺ y↓ +ᴺ x↓ +ᴺ y↓)
-ℚ_ : ℚ → ℚ
-ℚ record { numerator = n ; denominator-1 = d-1 ; isCoprime = isc } = {! (- n) ÷ d-1  !}

gcd>0 : ∀(m n : ℕ) → (n >ᴺ 0) → proj₁ (gcd m n) >ᴺ 0
gcd>0 zero (Sᴺ n) (s≤s n>0) with proj₁ (gcd 0 n)
... | gcd′ = ≤-suc n>0
gcd>0 (Sᴺ m) (Sᴺ n) (s≤s n>0) with gcd (Sᴺ m) n
gcd>0 (Sᴺ m) (Sᴺ n) (s≤s n>0) | zero , GCD.is (fst , snd) greatest = {!   !}
gcd>0 (Sᴺ m) (Sᴺ n) (s≤s n>0) | Sᴺ gcd′ , GCD.is commonDivisor greatest = {!   !}

-- constructs a rational number
buildℚ : ℤ → ℕ → ℚ
buildℚ (+_ num) denom with gcd num denom
buildℚ (+_ num) denom | gdcNum , gdcObj = {! + (num div gdcNum) / (denom div gdcNum)   !}
buildℚ (-[1+_] num) denom with gcd num denom
... | gcdobj = {!   !}

--Combines - and abs
diff : ℚ → ℚ → ℚ
diff x y with x Data.Rational.≤? y
diff x y | yes (*≤* x≤y) = y +ℚ (-ℚ x)
diff x y | no ¬p = x +ℚ (-ℚ y)

-- ε↑ *ᴺ (Sᴺ  )

-- data ℝ : Set where
--     ⟨_,_,_⟩ : (f   : ( ℕ → ℚ )) →
--               (ε→n : (ℚ → ℕ )) →
--               (∀(ε : ℚ) → ∀(a b : ℕ)
--                 → a >ᴺ (ε→n ε)
--                 → b >ᴺ (ε→n ε)
--                 → diff (f a) (f b) Data.Rational.≤ ε ) → ℝ

const : (x : ℚ) → (ℕ → ℚ) --Creates a constant function
const x = λ _ → x

--0ᵣ : ℝ
--0ᵣ = ⟨ const (+ 0 ÷ 1), ? , ? ⟩
