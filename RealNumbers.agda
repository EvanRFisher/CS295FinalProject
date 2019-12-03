open import Data.Rational.Unnormalised renaming (_+_ to _+ℚᵘ_) renaming (_-_ to _-ℚᵘ_) renaming (_*_ to _*ℚᵘ_) renaming (_>_ to _>ℚᵘ_) renaming (_<_ to _<ℚᵘ_) renaming (_≤_ to _≤ℚᵘ_)
open import Data.Nat renaming (_>_ to _>ᴺ_ ) renaming (_≤_ to _≤ᴺ_ ) renaming (suc to Sᴺ) renaming (_*_ to _*ᴺ_) renaming (_+_ to _+ᴺ_)
open import Data.Integer renaming (_*_ to _*ᶻ_)  renaming (suc to Sᶻ)
open import Data.Rational.Properties as ℚᵘprop
open import Data.Integer.Properties as ℤprop
open import Relation.Nullary
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality
--open import Axiom.Extensionality.Propositional as Extensionality


-- some interactions of rational operations and comparison not included in the standard library.
postulate
    sum[<] : ∀(a b c d : ℚᵘ) → a <ℚᵘ c → b <ℚᵘ d → a +ℚᵘ b <ℚᵘ (c +ℚᵘ d)




--
--
-- Real numbers are represented by cauchy sequences
-- And are thus a pair of a function f: ℕ → ℚᵘ
-- And a proof that ∀(ε : ℚᵘ). ∃ (n : ℕ). ∀(a,b : ℕ).
--                             a>n ∧ b>n → ∣ f(a) - f(b) ∣ < ε

infix 5 _∨_
data _∨_ (A B : Set) : Set where --From IC12
  Inl : A → A ∨ B
  Inr : B → A ∨ B

--abs
abs : ℚᵘ → ℚᵘ
abs (mkℚᵘ (+_ n) denom-1) = mkℚᵘ (+_ n) denom-1 -- Abs n = n if n>=0
abs (mkℚᵘ (-[1+_] n) denom-1) = mkℚᵘ (+_ (Sᴺ n)) denom-1 -- Abs -(1+a)/b = (a+1)/b if a<0

-- -[1+3] = -[1+-4]=3

data ℝ : Set where
 --⟪sequence,epsilon to number,proof⟫
    ⟪_,_,_⟫ : (f   : ( ℕ → ℚᵘ )) →
              (ε→n : (ℚᵘ → ℕ )) →
              (∀(ε : ℚᵘ) → ∀(a b : ℕ)
                → ε >ℚᵘ 0ℚᵘ
                → a >ᴺ (ε→n ε)
                → b >ᴺ (ε→n ε)
                → abs (f a -ℚᵘ f b) ≤ℚᵘ ε ) → ℝ

const : (x : ℚᵘ) → (ℕ → ℚᵘ) --Creates a constant function
const x = λ _ → x

const-inv : ∀ (x : ℚᵘ) → ∀ (n : ℕ) → const x n ≡ x
const-inv = λ x n → refl

-- 0ᵣ : ℝ
-- 0ᵣ with const (+ 0 / 1) | (λ x → 0) |
-- ... | 0ℚᵘ | const0 = ⟪ 0ℚᵘ , const0 , (λ ε a b ε>0 a>e→n b>e→n → *≤* {! ℤp.rop.*-zeroˡ (↧ ε)  !}) ⟫

--Helper proofs

mul[<] : ∀(a b : ℚᵘ) → a <ℚᵘ 1ℚᵘ → b >ℚᵘ 0ℚᵘ → a *ℚᵘ b <ℚᵘ b
mul[<] (mkℚᵘ (+_ n) den-1ᵃ) (mkℚᵘ numᵇ den-1ᵇ) (*<* a<1) (*<* b>0)      = *<* {!   !}
mul[<] (mkℚᵘ (-[1+_] n) den-1ᵃ) (mkℚᵘ numbᵇ den-1ᵇ) (*<* a<1) (*<* b>0) = *<* {!   !}

abs-+ : ∀(a b : ℚᵘ) → abs(a +ℚᵘ b) ≤ℚᵘ abs (a) +ℚᵘ abs(b)
abs-+ (mkℚᵘ (+_ n₁) denom-1₁) (mkℚᵘ (+_ n₂) denom-1₂) = {!   !}
abs-+ (mkℚᵘ (+_ n₁) denom-1₁) (mkℚᵘ (-[1+_] n₂) denom-1₂) = {!   !}
abs-+ (mkℚᵘ (-[1+_] n₁) denom-1₁) (mkℚᵘ (+_ n₂) denom-1₂) = {!   !}
abs-+ (mkℚᵘ (-[1+_] n₁) denom-1₁) (mkℚᵘ (-[1+_] n₂) denom-1₂) = {!   !}

-- Addition and multiplication


_+ʳ_ : ℝ → ℝ → ℝ
⟪ fᵃ , ε→nᵃ , prfᵃ ⟫ +ʳ ⟪ fᵇ , ε→nᵇ , prfᵇ ⟫  with (λ x → fᵃ x +ℚᵘ fᵇ x)  | (λ ε → ε→nᵃ ( ½ *ℚᵘ ε) +ᴺ ε→nᵇ ( ½ *ℚᵘ ε))
⟪ fᵃ , ε→nᵃ , prfᵃ ⟫ +ʳ ⟪ fᵇ , ε→nᵇ , prfᵇ ⟫ | fˣ | ε→nˣ = ⟪ fˣ , ε→nˣ ,
    (λ { ε a b ε>0 a>nˣ b>nˣ → {!   !}}) ⟫
                                                -- ⟪  -- Pointwise addition
                                                -- ,  -- Take the sum of the N's for εs half the size
                                                -- ,  ⟫
-- Want to prove that | (f a + g a) - (f b + g b) | ≤ ε
-- ⟶ ∣f a + g a - f b - g b∣
-- ⟶ ∣(f a - f b) + (g a - g b)∣
-- ● Need a proof that ∣ a + b ∣ ≤ ∣ a ∣ + ∣ b ∣
-- ⟶ ∣(f a - f b) ∣ + ∣ (g a - g b)∣
_×ʳ_ : ℝ → ℝ → ℝ
⟪ fᵃ , ε→nᵃ , prfᵃ ⟫ ×ʳ ⟪ fᵇ , ε→nᵇ , prfᵇ ⟫  with (λ x → fᵃ x *ℚᵘ fᵇ x) | inspect (λ x → fᵃ x *ℚᵘ fᵇ x) | (λ ε → ε→nᵃ ( ½ *ℚᵘ ε) *ᴺ ε→nᵇ ( ½ *ℚᵘ ε))
... | fˣ | fˣ₂ | ε→nˣ = ⟪ fˣ , ε→nˣ , (λ where ε a b ε>0 a>nˣ b>nˣ → {!   !}) ⟫
