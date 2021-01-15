{-# OPTIONS --type-in-type #-}

id : {A : Set} → A → A
id x = x

foo1 = let f = λ (_ : Set) → id                       in id {Set → Set → Set} f
-- foo2 = let f = λ (_ : Set) → (λ {A : Set}(x : A) → x) in id {Set → Set → Set} f

foo3 = (λ {A : Set}(x : A) → x) Set

const = λ {A : Set}({B : Set}(x : A)(y : B) → x

let id : {A : U} → A →  = λ x. x in

λ ?tel {x : A}

λ ?tel {x : A}. t
