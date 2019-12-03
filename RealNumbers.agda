open import Data.Rational.Unnormalised as ℚᵘmod renaming (_+_ to _+ℚᵘ_) renaming (_-_ to _-ℚᵘ_) renaming (_*_ to _*ℚᵘ_) renaming (_>_ to _>ℚᵘ_) renaming (_<_ to _<ℚᵘ_) renaming (_≤_ to _≤ℚᵘ_)
open import Data.Nat renaming (_>_ to _>ᴺ_ ) renaming (_≤_ to _≤ᴺ_ ) renaming (suc to Sᴺ) renaming (_*_ to _*ᴺ_) renaming (_+_ to _+ᴺ_)
open import Data.Integer renaming (_*_ to _*ᶻ_)  renaming (suc to Sᶻ) renaming (-_ to -ᶻ_)
open import Data.Rational.Properties as ℚprop
open import Data.Integer.Properties as ℤprop
open import Relation.Nullary
open import Agda.Builtin.Equality
--open import Relation.Binary.PropositionalEquality
open import Axiom.Extensionality.Propositional as Extensionality

-- Not used. Sometimes, Signs show up in targets, and renaming Data.Sign.Base.* to *Sign makes them more readable.
open import Data.Sign.Base renaming (_*_ to _*Sign_)



-- Definitions
infix 5 _∨_
data _∨_ (A B : Set) : Set where --From IC12
  Inl : A → A ∨ B
  Inr : B → A ∨ B

--abs
abs : ℚᵘ → ℚᵘ
abs (mkℚᵘ (+_ n) denom-1) = mkℚᵘ (+_ n) denom-1 -- Abs n = n if n>=0
abs (mkℚᵘ (-[1+_] n) denom-1) = mkℚᵘ (+_ (Sᴺ n)) denom-1 -- Abs -(1+a)/b = (a+1)/b if a<0

data ℝ : Set where
 --⟪sequence,epsilon to number,proof⟫
    ⟪_,_,_⟫ : (f   : ( ℕ → ℚᵘ )) →
              (ε→n : (ℚᵘ → ℕ )) →
              (∀(ε : ℚᵘ) → ∀(a b : ℕ)
                → ε >ℚᵘ 0ℚᵘ
                → a >ᴺ (ε→n ε)
                → b >ᴺ (ε→n ε)
                → abs (f a -ℚᵘ f b) ≤ℚᵘ ε ) → ℝ
                -- Real numbers are represented by cauchy sequences
                -- And are thus a pair of a function f: ℕ → ℚᵘ
                -- And a proof that ∀(ε : ℚᵘ). ∃ (n : ℕ). ∀(a,b : ℕ).
                --                             a>n ∧ b>n → ∣ f(a) - f(b) ∣ < ε

f←_ : ℝ → (ℕ → ℚᵘ)
f← ⟪ f , ε→n , x ⟫ = f

infix 4 _≃ʳ_
data _≃ʳ_ : ℝ → ℝ → Set where
    *≡* : ∀ {p q : ℝ} → (ε→n : (ℚᵘ → ℕ )) → (∀(ε : ℚᵘ) → ∀(a : ℕ) → ε >ℚᵘ 0ℚᵘ → a >ᴺ (ε→n ε) → abs ((f← p) a -ℚᵘ (f← q) a) ≤ℚᵘ ε ) → p ≃ʳ q
-- If ∀ε,∃N such that the two sequences are always less than ε apart for all indexes > N, the two converge to the same value and are equal.



const : (x : ℚᵘ) → (ℕ → ℚᵘ) --Creates a constant function
const x = λ _ → x

const-inv : ∀ (x : ℚᵘ) → ∀ (n : ℕ) → const x n ≡ x
const-inv = λ x n → refl

--Postulates

-- Some interactions of rational operations and comparison not included in the standard library, as well as some properties of abs.
-- Unnormalized natural numbers, while somewhat easier to work with, have less support, so most properties are postulated here.
postulate
    sum[<] : ∀(a b c d : ℚᵘ) → a <ℚᵘ c → b <ℚᵘ d → a +ℚᵘ b <ℚᵘ (c +ℚᵘ d)
    abs-split[+/≤] : ∀(a b : ℚᵘ) → abs(a +ℚᵘ b) ≤ℚᵘ abs (a) +ℚᵘ abs(b)

-- Properties of ≤ and < over ℚᵘ. Adjusted from agda basics-002
postulate
    xRx[≤] : ∀ (m : ℚᵘ) → m ≤ℚᵘ m
    _⊚[≤]_ : ∀ {m n p : ℚᵘ} → n ≤ℚᵘ p → m ≤ℚᵘ n → m ≤ℚᵘ p
    _⋈[≤]_ : ∀ {m n : ℚᵘ} → m ≤ℚᵘ n → n ≤ℚᵘ m → m ≡ n
    _⊚[<]_ : ∀ {m n p : ℚᵘ} → n <ℚᵘ p → m <ℚᵘ n → m <ℚᵘ p
    _⊚[</≤]_ : ∀ {m n p : ℚᵘ} → n <ℚᵘ p → m ≤ℚᵘ n → m <ℚᵘ p
    _⊚[≤/<]_ : ∀ {m n p : ℚᵘ} → n ≤ℚᵘ p → m <ℚᵘ n → m <ℚᵘ p
    lmono[+/≤] : ∀ (x x′ y : ℚᵘ) → x ≤ℚᵘ x′ → x +ℚᵘ y ≤ℚᵘ x′ +ℚᵘ y
    rmono[+/≤] : ∀ (x y y′ : ℚᵘ) → y ≤ℚᵘ y′ → x +ℚᵘ y ≤ℚᵘ x +ℚᵘ y′
    lmono[+/<] : ∀ (x x′ y : ℚᵘ) → x <ℚᵘ x′ → x +ℚᵘ y <ℚᵘ x′ +ℚᵘ y
    rmono[+/<] : ∀ (x y y′ : ℚᵘ) → y <ℚᵘ y′ → x +ℚᵘ y <ℚᵘ x +ℚᵘ y′

-- Properties of + and * over ℚᵘ. Adjusted from agda basics-002
postulate
    lunit[+] : ∀ (m : ℚᵘ) → 0ℚᵘ +ℚᵘ m ≡ m
    runit[+] : ∀ (m : ℚᵘ) → m +ℚᵘ 0ℚᵘ ≡ m
    assoc[+] : ∀ (m n p : ℚᵘ) → m +ℚᵘ (n +ℚᵘ p) ≡ (m +ℚᵘ n) +ℚᵘ p
    commu[+] : ∀ (m n : ℚᵘ) → m +ℚᵘ n ≡ n +ℚᵘ m
    lunit[×] : ∀ (m : ℚᵘ) → 1ℚᵘ *ℚᵘ m ≡ m
    runit[×] : ∀ (m : ℚᵘ) → m *ℚᵘ 1ℚᵘ ≡ m
    lzero[×] : ∀ (m : ℚᵘ) → 0ℚᵘ *ℚᵘ m ≡ 0ℚᵘ
    rzero[×] : ∀ (m : ℚᵘ) → m *ℚᵘ 0ℚᵘ ≡ 0ℚᵘ
    assoc[×] : ∀ (m n p : ℚᵘ) → m *ℚᵘ (n *ℚᵘ p) ≡ (m *ℚᵘ n) *ℚᵘ p
    commu[×] : ∀ (m n : ℚᵘ) → m *ℚᵘ n ≡ n *ℚᵘ m
    ldist[×] : ∀ (m n p : ℚᵘ) → m *ℚᵘ (n +ℚᵘ p) ≡ m *ℚᵘ n +ℚᵘ m *ℚᵘ p
    rdist[×] : ∀ (m n p : ℚᵘ) → (m +ℚᵘ n) *ℚᵘ p ≡ m *ℚᵘ p +ℚᵘ n *ℚᵘ p
    distr[-] : ∀ (m n p : ℚᵘ) → m -ℚᵘ (n +ℚᵘ p) ≡ m -ℚᵘ n -ℚᵘ p
    inver[+] : ∀ (m : ℚᵘ) → (m -ℚᵘ m) ≡ 0ℚᵘ


0ᵣ : ℝ
0ᵣ with (λ x → 0)
... | const0 = ⟪ (λ x → 0ℚᵘ) , const0 , (λ ε a b ε>0 a>e→n b>e→n → *≤* {! ℤprop.*-zeroˡ (↧ ε)  !}) ⟫

--Helper proofs

-- Addition and multiplication

-- look at that type. Whew.
add-helper : (f₁ : ( ℕ → ℚᵘ )) → (ε→n₁ : (ℚᵘ → ℕ )) → (∀(ε₁ : ℚᵘ) → ∀(a₁ b₁ : ℕ) → ε₁ >ℚᵘ 0ℚᵘ → a₁ >ᴺ (ε→n₁ ε₁) → b₁ >ᴺ (ε→n₁ ε₁) → abs (f₁ a₁ -ℚᵘ f₁ b₁) ≤ℚᵘ ε₁ ) →
             (f₂ : ( ℕ → ℚᵘ )) → (ε→n₂ : (ℚᵘ → ℕ )) → (∀(ε₂ : ℚᵘ) → ∀(a₂ b₂ : ℕ) → ε₂ >ℚᵘ 0ℚᵘ → a₂ >ᴺ (ε→n₂ ε₂) → b₂ >ᴺ (ε→n₂ ε₂) → abs (f₂ a₂ -ℚᵘ f₂ b₂) ≤ℚᵘ ε₂ ) →
             ∀(εₓ : ℚᵘ) → ∀(aₓ bₓ : ℕ) → εₓ >ℚᵘ 0ℚᵘ → aₓ >ᴺ ((λ ε → ε→n₁ ( ½ *ℚᵘ ε) +ᴺ ε→n₂ ( ½ *ℚᵘ ε)) εₓ) → bₓ >ᴺ ((λ ε → ε→n₁ ( ½ *ℚᵘ ε) +ᴺ ε→n₂ ( ½ *ℚᵘ ε)) εₓ) →
             abs ((λ x → f₁ x +ℚᵘ f₂ x) aₓ -ℚᵘ (λ x → f₁ x +ℚᵘ f₂ x) bₓ) ≤ℚᵘ εₓ

add-helper fᵃ ε→nᵃ prfᵃ fᵇ ε→nᵇ prfᵇ εₓ aₓ bₓ εₓ>0 aₓ>ε bₓ>ε rewrite distr[-] (fᵃ aₓ +ℚᵘ fᵇ bₓ) (fᵃ aₓ) (fᵇ bₓ)
                                                                   | commu[+] (fᵃ aₓ) (fᵇ bₓ)
                                                                   | assoc[+] (fᵇ bₓ) (fᵃ aₓ) (ℚᵘmod.- fᵃ aₓ)
                                                                   | inver[+] (fᵃ aₓ) = {!   !}


_+ʳ_ : ℝ → ℝ → ℝ
⟪ fᵃ , ε→nᵃ , prfᵃ ⟫ +ʳ ⟪ fᵇ , ε→nᵇ , prfᵇ ⟫  with (λ x → fᵃ x +ℚᵘ fᵇ x)  | (λ ε → ε→nᵃ ( ½ *ℚᵘ ε) +ᴺ ε→nᵇ ( ½ *ℚᵘ ε)) | add-helper fᵃ ε→nᵃ prfᵃ fᵇ ε→nᵇ prfᵇ
⟪ fᵃ , ε→nᵃ , prfᵃ ⟫ +ʳ ⟪ fᵇ , ε→nᵇ , prfᵇ ⟫ | fˣ | ε→nˣ | prfₓ = ⟪ fˣ , ε→nˣ , {!  !} ⟫
                                                -- ⟪  -- Pointwise addition
                                                -- ,  -- Take the sum of the N's for εs half the size
                                                -- ,  ⟫
-- Want to prove that | (f a + g a) - (f b + g b) | ≤ ε
-- ⟶ ∣f a + g a - f b - g b∣
-- ⟶ ∣(f a - f b) + (g a - g b)∣
-- ● Need a proof that ∣ a + b ∣ ≤ ∣ a ∣ + ∣ b ∣
-- ⟶ ∣(f a - f b) ∣ + ∣ (g a - g b)∣

-ᵣ_ : ℝ → ℝ
-ᵣ ⟪ f , ε→n , prf ⟫ = ⟪ (λ x → ℚᵘmod.- f x) , ε→n , (λ ε a b ε>0 a>ε b>ε → {!   !}) ⟫

-- Addition Lemmas
commu-helper : ∀ (f₁ f₂ : (ℕ → ℚᵘ)) → ∀ (a : ℕ) → abs (f₁ a +ℚᵘ f₂ a -ℚᵘ (f₂ a +ℚᵘ f₁ a)) ≡ 0ℚᵘ
commu-helper f g a with f a | g a | ℚᵘmod.- g a | ℚᵘmod.- f a
... | fa | ga | nga | nfa rewrite distr[-] (fa +ℚᵘ ga) (ga) (fa) | assoc[+] (fa) (ga) (nga +ℚᵘ nfa) | assoc[+] (ga) (nga) (nfa) | inver[+] (ga) | lunit[+] nfa = {!   !}

commu-helper′ : ∀ (f₁ f₂ : (ℕ → ℚᵘ)) → ∀ (a : ℕ) → ∀ (ε : ℚᵘ) → abs (f₁ a +ℚᵘ f₂ a -ℚᵘ (f₂ a +ℚᵘ f₁ a)) ≤ℚᵘ ε
commu-helper′ f g a ε rewrite commu-helper f g a | ℤprop.*-zeroˡ (↧ ε) = *≤* {! ℤprop.*-zeroˡ (↧ ε)!}



-- Addition Properties

commu[+ʳ] : ∀ (a b : ℝ ) → a +ʳ b ≃ʳ b +ʳ a
commu[+ʳ] ⟪ f₁ , ε→n₁ , prf₁ ⟫ ⟪ f₂ , ε→n₂ , prf₂ ⟫ = *≡* (λ x → 0) λ where ε a ε>0 a>0 → {!   !}

assoc[+ʳ] : ∀ (a b c : ℝ ) → a +ʳ (b +ʳ c) ≃ʳ (a +ʳ b) +ʳ c
assoc[+ʳ] a b c = *≡* (λ x → 0) (λ ε n ε>0 n>0 → {!   !})

lzero[+ʳ] : ∀ (a : ℝ) → (0ᵣ +ʳ a ≃ʳ a)
lzero[+ʳ] a = {!   !}

inver[+ʳ] : ∀ (a : ℝ) → (a +ʳ (-ᵣ a) ≃ʳ 0ᵣ)
inver[+ʳ] a = {!   !}

--Multiplication
_×ʳ_ : ℝ → ℝ → ℝ
⟪ fᵃ , ε→nᵃ , prfᵃ ⟫ ×ʳ ⟪ fᵇ , ε→nᵇ , prfᵇ ⟫  with (λ x → fᵃ x *ℚᵘ fᵇ x) | (λ ε → ε→nᵃ ( ½ *ℚᵘ ε) *ᴺ ε→nᵇ ( ½ *ℚᵘ ε))
... | fˣ | ε→nˣ = ⟪ fˣ , ε→nˣ , (λ where ε a b ε>0 a>nˣ b>nˣ → {!   !}) ⟫
