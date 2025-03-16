{-# OPTIONS  --backtracking-instance-search  #-}
module Example.IO where

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Equality
open import Agda.Primitive

open import Mystdlib.Mystdlib

open import Effect.Core.Free hiding ( _>>=_ ; _>>_ )

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

record Effect2 {a b : Level} : Set (lsuc (a ⊔ b)) where -- (a ⊔ b) where
 field Op  : Set a
       Ret : Op -> Set b
open Effect2 public

data IOOP : Set1 where
  liftIO  : (A : Set) -> IO A ->  IOOP


IOEF : Effect2
IOEF .Op = IOOP
IOEF .Ret (liftIO ty x) = ty


data Free2 {a b : Level} (eff : Effect2 {a} {b}) ( A : Set b) : Set (lsuc (a ⊔ b)) where
    pure   : A                                                -> Free2 eff A
    impure : (op : Op eff) -> (k : Ret eff op -> Free2 eff A) -> Free2 eff A



data Sum2 {a : Level} (A : Set a) (B : Set a) : Set ((a)) where
  injl : (x : A) → Sum2 A B
  injr : (y : B) → Sum2 A B

elim2 :
        {a : Level}
        {C : Sum2 A B → Set (lsuc a)} →    -- it is a box
        ((x : A) → C (injl x)) → -- it is a function to convert left case to box
        ((x : B) → C (injr x)) → -- it is a function to convert right case to box
        (x : Sum2 A  B)             -- it is a what we can move to box
        → C x                     -- result
elim2 f g (injl x) = f x
elim2 f g (injr y) = g y


coProduct2 : {a b : Level} -> Effect2 {a} {b} -> Effect2 {a} {b} -> Effect2 {a} {b}
coProduct2 {a} {b} x y .Op = Sum2 {a} (Op x) (Op y)
coProduct2 {a} {b} x y .Ret (injl x1) = Ret x x1
coProduct2 {a} {b} x y .Ret (injr y1) = Ret y y1

infixr 12 _|2>_
_|2>_ : {a b : Level} -> Effect2 {a} {b} -> Effect2 {a} {b} -> Effect2 {a} {b}
_|2>_ = coProduct2

postulate
    putCharIO : Char -> IO ⊤
    getCharIO : IO Char
    readFileIO  : String -> IO String
    writeFileIO : String -> String -> IO ⊤
    return : A → IO A
    _>>>=_  : IO A → (A → IO B) → IO B
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified System.IO as SIO #-}
{-# COMPILE GHC putCharIO = (SIO.hPutChar SIO.stderr) #-}
{-# COMPILE GHC getCharIO = SIO.getChar #-}
{-# COMPILE GHC writeFileIO = \ path text -> writeFile (T.unpack path) (T.unpack text) #-}
{-# COMPILE GHC readFileIO = \ path ->  readFile (T.unpack path) >>= \ text -> return (T.pack text) #-}
{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>>=_  = \_ _ _ _ -> (>>=) #-}

infixl 1 _>>>_
_>>>_ : IO A → IO B → IO B
a >>> b = a >>>= λ _ → b




program1 : Free2 IOEF ⊤
program1 = impure (liftIO Char getCharIO) \ x ->
           impure (liftIO Char getCharIO) \ y ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           pure tt



--How does it use?
data EffectStorage2 {a b : Level} :
                       Effect2 {a} {b}
                    -> Effect2 {a} {b}
                    -> Effect2 {a} {b}
                    -> Set (lsuc (a ⊔ b))
                    where
    insert  : {Here There : Effect2 {a} {b}}
            -> EffectStorage2 {a} {b} (coProduct2 Here There) Here There
    sift  : {E Here Next There : Effect2 {a} {b}}
            -> EffectStorage2 {a} {b} E Here There
            -> EffectStorage2 {a} {b} (coProduct2 Next E) Here (coProduct2 Next There)

instance
  insert21 : {a b : Level}
            -> {Here There : Effect2 {a} {b}}
            -> EffectStorage2 {a} {b} (coProduct2 Here There) Here There
  insert21 = insert

  sift21 : {a b : Level}
          {E Here Next There : Effect2 {a} {b}}
        -> {{EffectStorage2 E Here There}}
        -> (EffectStorage2 (coProduct2 Next E) Here (coProduct2 Next There))
  sift21 ⦃ w ⦄ = sift w



--I need to rename this
inj-insert-left2 : {a b : Level} {E Here There : Effect2 {a} {b}}
                  {{ w : EffectStorage2 E Here There }}
                  -> Op Here
                  -> Op E
inj-insert-left2 {{ insert }} op = injl op
inj-insert-left2 {{ sift w }} op = injr (inj-insert-left2 {{w}} op)

inj-insert-right2 :  {a b : Level} {E Here There : Effect2 {a} {b}} {{ w : EffectStorage2 E Here There }}  -> Op There -> Op E
inj-insert-right2 {{ insert }} op = injr op
inj-insert-right2 {{ w = sift w }} (injl next) = injl next
inj-insert-right2 {{ w = sift w }} (injr there) = injr (inj-insert-right2 {{w}} there)


--I need to rename this
proj-ret-left2 : {a b : Level}
        {E Here There : Effect2 {a} {b}}
        -> {{ w : EffectStorage2 E Here There }}
        -> {op : Op Here}
        -> Ret E (inj-insert-left2 op)
        -> Ret Here op
proj-ret-left2 {{ insert }} x = x
proj-ret-left2 {{ sift w }} x = proj-ret-left2 {{w}} x


--I need to rename this
proj-ret-right2 : {a b : Level}
        {E Here There : Effect2 {a} {b}}
        -> {{ w : EffectStorage2 E Here There }}
        -> {op : Op There}
        -> Ret E (inj-insert-right2 op)
        -> Ret There op
proj-ret-right2 {{ insert }} x =  x
proj-ret-right2 ⦃ w = sift w ⦄ {injl next } x = x
proj-ret-right2 ⦃ w = sift w ⦄ {injr op} x = proj-ret-right2 {{w}} x

injl-ret-eq2 : {a b : Level}
        {E Here There : Effect2 {a} {b}}
        -> {{ w : EffectStorage2 E Here There }}
        -> (op : Op Here)
        -> Ret E (inj-insert-left2 op) ≡ Ret Here op
injl-ret-eq2 ⦃ insert ⦄ _ = refl
injl-ret-eq2 ⦃ sift w ⦄ = injl-ret-eq2 {{w}}

injr-ret-eq2 : {a b : Level}
        {E Here There : Effect2 {a} {b}}
        -> {{ w : EffectStorage2 E Here There }}
        -> (op : Op There)
        -> Ret E (inj-insert-right2 op) ≡ Ret There op
injr-ret-eq2 ⦃ insert ⦄ _ = refl
injr-ret-eq2 ⦃ w = sift w ⦄ (injl x) = refl
injr-ret-eq2 ⦃ w = sift w ⦄ (injr y) = injr-ret-eq2 {{w}} y

case2 :  {a b : Level} {E Here There : Effect2 {a} {b}}
       -> {{ w : EffectStorage2 E Here There }}
        -> Op E
        -> (Op Here -> A )
        -> (Op There -> A )
        -> A
case2 {{ w = insert }} (injl here) fromHere fromThere = fromHere here
case2 {{ w = insert }} (injr there) fromHere fromThere = fromThere there
case2 {{ w = sift w }} (injl there) fromHere fromThere = fromThere (injl there)
case2 {{ w = sift w }} (injr e) fromHere fromThere = case2 {{w}} e fromHere λ there -> fromThere (injr there)

case-eq2 :  {a b : Level}{E Here There : Effect2 {a} {b}}
       -> {{ w : EffectStorage2 E Here There }}
        -> (op : Op E)
        -> ((op' : Op Here)  -> (op ≡ inj-insert-left2  op') -> A)
        -> ((op' : Op There) -> (op ≡ inj-insert-right2 op') -> A)
        -> A
case-eq2 {{ w = insert }} (injl x) eq-here eq-there = eq-here  x refl
case-eq2 {{ w = insert }} (injr y) eq-here eq-there = eq-there y refl
case-eq2 {{ w = sift w }} (injl x) eq-here eq-there = eq-there (injl x) refl
case-eq2 {{ w = sift w }} (injr e) eq-here eq-there =
    case-eq2 {{w}} e
        (λ  here eq -> eq-here  here (cong injr eq))
        (λ there eq -> eq-there (injr there) (cong injr eq))

subst2 : {a : Level} {A : Set a} {x y : A} (P : A → Set b)
  → x ≡ y
    ---------
  → P x → P y
subst2 P refl px = px



help21 :  {a b : Level} {E Here There : Effect2 {a} {b}}
       -> {{ w   : EffectStorage2 E Here There }}
       -> (  op' : Op Here)
       -> (  op  : Op E)
       -> (  eq  : op ≡ inj-insert-left2 op')
       -> Ret Here op'
       -> Ret E    op
help21 {a} {b} {E} {Here} ⦃ w ⦄ op' op eq = subst2 {b} id (begin
        Ret Here op'
        ≡⟨ sym (injl-ret-eq2 {{w}} op')  ⟩
        Ret E (inj-insert-left2 op')
        ≡⟨ sym (cong (Ret E) eq)  ⟩
        Ret E op
        ∎)

help22 :  {a b : Level} {E Here There : Effect2 {a} {b}}
       -> {{ w   : EffectStorage2 E Here There }}
       -> (  op' : Op There)
       -> (  op  : Op E)
       -> (  eq  : op ≡ inj-insert-right2 op')
       -> Ret There op'
       -> Ret E    op
help22 {a} {b} {E} {Here} {There} ⦃ w ⦄ op' op eq = subst2 {b} id (begin
        Ret There op'
        ≡⟨ sym (injr-ret-eq2 {{w}} op')  ⟩
        Ret E (inj-insert-right2 op')
        ≡⟨ sym (cong (Ret E) eq)  ⟩
        Ret E op
        ∎)

-- What doest it do?
-- How doest it do?
to-front2 :  {a b : Level} {E Here There : Effect2 {a} {b}}
          -> {A : Set b}
          -> {{ w : EffectStorage2 E Here There }}
          -> Free2 E A
          -> Free2 (coProduct2 Here There) A
to-front2 ⦃ w = w ⦄ (pure x) = pure x
to-front2 ⦃ w = insert ⦄ (impure op k) = impure op
                            (λ x -> to-front2 {{insert}} (k x))
to-front2 ⦃ w = sift w ⦄ (impure (injl op) k) =
    impure (injr (injl op)) (λ x -> to-front2 {{sift w}} (k x))
to-front2 { Here = Here } {{ sift {E = E} {There = There} w }} (impure (injr op) k) = case-eq2 {{ w }} op
    (λ op' eq -> impure (injl op') λ x -> to-front2 {{sift w}} (k (help21  {{w}} op' op eq x)))
    (λ op' eq -> impure (injr (injr op')) λ x -> to-front2 {{sift w}} (k (help22 {{w}} op' op eq x)))

-- I am not sure about levels
Alg2 : {a b : Level }(Eff : Effect2 {a} {b}) -> (A : Set b) -> Set (a ⊔ b)
Alg2 Eff A = (op : Op Eff)(k : Ret Eff op -> (A)) -> A

fold2 : {a b : Level } {A : Set b} {B : Set b} {Eff : Effect2 {a} {b}}
        -> (A -> B)
        -> Alg2 Eff B
        -> Free2 {a} {b} Eff A
        -> B
fold2 g alg (pure x) = g x
fold2 g alg (impure op k) = alg op λ x -> fold2 g alg (k x)


Alg3 : {a b : Level }(Eff : Effect2 {a} {b}) -> (A : Set (lsuc a ⊔ lsuc b)) -> Set (lsuc a ⊔ lsuc b)
Alg3 Eff A = (op : Op Eff)(k : Ret Eff op -> (A)) -> A

fold3 : {a b : Level } {A : Set b} {B : Set (lsuc a  ⊔ lsuc b)} {Eff : Effect2 {a} {b}}
        -> (A -> B)
        -> Alg3 Eff B
        -> Free2 {a} {b} Eff A
        -> B
fold3 g alg (pure x) = g x
fold3 g alg (impure op k) = alg op λ x -> fold3 g alg (k x)

-- How does it work?
_>>=_ : {a b : Level} {A : Set b} {B : Set b}
        {Eff : Effect2 {a} {b}} -> Free2 Eff A -> (A -> Free2 Eff B) -> Free2 Eff B
m >>= g = fold3 g impure m

-- How does it work?
_>>_ : {a b : Level} {A : Set b} {B : Set b}
       {Eff : Effect2 {a} {b}} ->
     Free2 Eff A → Free2 Eff B → Free2 Eff B
m1 >> m2 = m1 >>= λ _ → m2



record Handler2 {a b : Level}
                (A : Set b)
                (E : Effect2 {a} {b})
                (P : Set b)
                (B : Set b)
                (Continue : Effect2 {a} {b})
                : Set (lsuc (a ⊔ b))
                where
    field ret : A -> P -> Free2 Continue B
          hdl : Alg3 E (P -> Free2 Continue B)
open Handler2 public

givenHandle2 : {a b : Level}
            {A : Set b}
            {B : Set b}
            {P : Set b}
            -> {E Here There : Effect2 {a} {b}}
            -> {{ EffectStorage2 E Here There  }}
            -> Handler2 A Here P B There
            -> Free2 E A
            -> (P -> Free2 {a} {b} There B)
givenHandle2 {a} {b} {A} {B} {P} {E} {Here} {There} h eff =
    fold3 (ret h) func (to-front2 eff) where
    func : Alg3 (coProduct2 Here There) (P -> Free2 {a} {b} There B)
    func  (injl op) k p = hdl h op k p
    func (injr op) k p = impure op (λ x → k x p)

execAlgebra2 : Alg2 IOEF (IO A)
execAlgebra2 (liftIO ty f) k = f >>>= k

exec2 : Free2 IOEF A -> IO A
exec2 = fold2 return execAlgebra2

main1 : IO ⊤
main1 = exec2 program1

`liftIO :
      {E Here : Effect2 }
     -> {{ EffectStorage2 E Here IOEF}}
     -> {A : Set}
     -> (f : IO A)
     -> Free2 E A
`liftIO {{ w }} {A} f = impure (inj-insert-right2 (liftIO A f)) (\ x -> pure (proj-ret-right2 {{w}} x))

putStrLn : {E Here : Effect2}
          -> {{ EffectStorage2 E Here IOEF }}
          -> String
          -> Free2 E ⊤
putStrLn x = f (primStringToList x) where
  f : List Char
    -> {E Here : Effect2}
    -> {{ EffectStorage2 E Here IOEF }}
    -> Free2 E ⊤
  f [] =  `liftIO (putCharIO '\n') -- `putChar '\n'
  f (x ∷ str) = do
    `liftIO (putCharIO x) -- `putChar x
    f str

data StateOp : Set1 where
    get : StateOp
    put : Char -> StateOp

State : Effect2
Op  State = StateOp
Ret State get = Char
Ret State (put x) = ⊤

hSt : {Eff : Effect2} -> Handler2 A State Char ( A × Char ) Eff
ret hSt x s = pure (x , s)
hdl hSt get k n = k n n
hdl hSt (put m) k _ = k tt m


`put :
      {E There : Effect2}
     -> {{ EffectStorage2 E State There }}
     -> Char
     -> Free2 E ⊤
`put {{ w }} n = impure (inj-insert-left2 (put n) ) (λ x -> pure (proj-ret-left2 {{w}} x))

`get :
      {E There : Effect2}
     -> {{ EffectStorage2 E State There }}
     -> Free2 E Char
`get {{ w }}  = impure (inj-insert-left2 get ) (λ x -> pure (proj-ret-left2 {{w}} x))

program : Free2 (coProduct2 State IOEF) ⊤
program = do
    putStrLn "Check def"
    def <- `get
    `liftIO (putCharIO def)
    `put 'a'
    a   <- `get
    putStrLn "\nCheck State"
    `liftIO (putCharIO a)
    putStrLn "\n"
    h1  <- `liftIO (getCharIO)
    `liftIO (putCharIO h1)
    `liftIO (putCharIO h1)
    `liftIO (putCharIO h1)
    `liftIO (putCharIO h1)
    putStrLn "Put2"
    h2  <- `liftIO (getCharIO)
    `liftIO (putCharIO h2)
    `liftIO (putCharIO h2)
    `liftIO (putCharIO h2)
    `liftIO (putCharIO h2)
    putStrLn "Put3"

main2 : IO ⊤
main2 = exec2 (givenHandle2 hSt program 'z') >>>= \ x -> return tt

data TeletypeOp : Set1 where
  putChar  : Char   -> TeletypeOp
  getChar  : TeletypeOp

Teletype : Effect2
Teletype .Op              = TeletypeOp
Teletype .Ret (putChar x) = ⊤
Teletype .Ret getChar     = Char

hTeletype : Handler2 A Teletype ⊤ ( ⊤ ) IOEF
hTeletype .ret _ _ = pure tt
hTeletype .hdl (putChar ch) k _ = impure (liftIO ⊤ (putCharIO ch)) (k tt )
hTeletype .hdl getChar k _      = impure (liftIO Char (getCharIO)) \ ch -> k ch tt


`putChar :
      {E There : Effect2}
     -> {{ EffectStorage2 E Teletype There}}
     -> Char
     -> Free2 E ⊤
`putChar {{ w }} ch = impure (inj-insert-left2 (putChar ch)) (λ x -> pure (proj-ret-left2 {{w}} x))

`getChar :
      {E There : Effect2}
     -> {{ EffectStorage2 E Teletype There}}
     -> Free2 E Char
`getChar {{ w }} = impure (inj-insert-left2 getChar) (λ x -> pure (proj-ret-left2 {{w}} x))




program2 : Free2 (coProduct2 Teletype IOEF) ⊤
program2 = do
    `liftIO (putCharIO 'h')
    `liftIO (putCharIO 'e')
    `liftIO (putCharIO 'l')
    `liftIO (putCharIO 'l')
    `liftIO (putCharIO 'l')
    `liftIO (putCharIO '0')
    `liftIO (putCharIO '\n')
    `putChar 'h'
    `putChar 'e'
    `putChar 'l'
    `putChar 'l'
    `putChar 'o'
    `putChar '\n'
    ch <- `getChar
    ch2 <- `getChar
    `liftIO (putCharIO ch)
    `liftIO (putCharIO ch)
    `liftIO (putCharIO ch2)
    `liftIO (putCharIO ch2)

main3 : IO ⊤
main3 = exec2 (givenHandle2 hTeletype program2 tt) >>>= \ x -> return tt


data FileSystemOp : Set1 where
  ReadFile   : String -> FileSystemOp
  WriteFile  : String -> String -> FileSystemOp

Filesystem : Effect2
Filesystem .Op                        = FileSystemOp
Filesystem .Ret (ReadFile file)       = String
Filesystem .Ret (WriteFile file text) = ⊤



readFile :
      {E There : Effect2}
     -> {{ EffectStorage2 E Filesystem There}}
     -> String
     -> Free2 E String
readFile {{ w }} path = impure (inj-insert-left2 (ReadFile path)) (λ x -> pure (proj-ret-left2 {{w}} x))

writeFile :
      {E There : Effect2}
     -> {{ EffectStorage2 E Filesystem There}}
     -> String
     -> String
     -> Free2 E ⊤
writeFile {{ w }} path text = impure (inj-insert-left2 (WriteFile path text)) (λ x -> pure (proj-ret-left2 {{w}} x))

putStrLn2 : {E There : Effect2}
          -> {{ EffectStorage2 E Teletype There }}
          -> String
          -> Free2 E ⊤
putStrLn2 x = f (primStringToList x) where
  f : List Char
    -> {E There : Effect2}
    -> {{ EffectStorage2 E Teletype There}}
    -> Free2 E ⊤
  f [] =  `putChar '\n'
  f (x ∷ str) = do
    `putChar x
    f str



program3 : Free2 (Filesystem |2> Teletype |2> IOEF) ⊤
program3 = do
  file <- readFile "test.txt"
  putStrLn2 file


hFilesystem :  {Eff : Effect2} -> Handler2 A Filesystem ⊤ ( ⊤ ) (Eff |2> IOEF)
hFilesystem .ret _ _ = pure tt
hFilesystem .hdl (ReadFile path) k _       =
  impure (injr (liftIO String (readFileIO path))) \ ch -> k ch tt
hFilesystem .hdl (WriteFile path text) k _ =
  impure (injr (liftIO ⊤ (writeFileIO path text))) (k tt )


main : IO ⊤

main = exec2 (givenHandle2 hTeletype
            (givenHandle2 hFilesystem program3 tt) tt) >>>= \ x -> return tt
