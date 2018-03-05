Pair = λA::*.λB::*.∀C::*.(A -> B -> C) -> C;

pair = ΛA::*.ΛB::*.λx:A.λy:B.ΛC::*.λk:(A -> B -> C).k x y;

fst = ΛA::*.ΛB::*.λp:Pair A B.p [A] (λx:A.λy:B.x);

snd = ΛA::*.ΛB::*.λp:Pair A B.p [B] (λx:A.λy:B.y);      

# Some standard definitions.  Any definition in this file may be used
# in the solution to any question

# The empty type, Zero.
# There is no value of type Zero.
# From a variable of type Zero it is possible to build a term of any type:
#   λx:Zero. x [A]
Zero :: *
     = ∀α.α;

# The one-element type Unit, and its single inhabitant, unit.
Unit :: *
     = ∀A::*.A → A;
unit = ΛA.λa:A.a;

# The two element type Bool, its two inhabitants, ff (false) and tt (true),
# and its destructor, if.
Bool :: * = ∀A::*.A → A → A;
ff : Bool 
   = ΛA.λf:A.λt:A.f;
tt : Bool 
   = ΛA.λf:A.λt:A.t;
if : Bool → (∀α.α → α → α)
   = λb:Bool.b;

# The type of natural numbers, Nat, along with
# its two constructors zero and succ, and an addition function, add.
Nat :: * =
 ∀α::*.α → (α → α) → α;
zero : Nat
  = Λα::*.λz:α.λs:α → α.z;
succ : Nat → Nat
  = λn:Nat.Λα::*.λz:α.λs:α → α.s (n [α] z s);
add : Nat → Nat → Nat
  = λm:Nat.λn:Nat.m [Nat] n succ;


# 1(a): (answer on paper)
# 1(b): (answer on paper)
# 1(c): (answer on paper)
# 2(a): (answer on paper)
# 2(b): (answer on paper)

# 3(a)
#  (a + b) + c ≃ a + (b + c)
plus_assoc1 : ∀A.∀B.∀C.((A + B) + C) → (A + (B + C))
           =  ΛA.ΛB.ΛC.λabc: (A+B)+C.
              case abc of
                  ab. (case ab of a. inl [B+C] a | b. inr [A] (inl [C] b))
                  | c. inr [A] (inr [B] c) 
;
plus_assoc2 : ∀A.∀B.∀C.(A + (B + C)) → ((A + B) + C)
           = ΛA.ΛB.ΛC.λabc: A+(B+C).
              case abc of
                  a. inl [C] (inl [B] a)
                  | bc. (case bc of b. inl [C] (inr [A] b) | c. inr [A+B] c)
;

# 3(b)
# a(b + c) ≃ ab + ac
distrib1 : ∀A.∀B.∀C.(A×(B + C)) → ((A×B) + (A×C))
           = ΛA.ΛB.ΛC.λs: A×(B+C).
                case @2 s of 
                    b. inl [A×C] ⟨@1 s, b⟩
                  | c. inr [A×B] ⟨@1 s, c⟩

;
distrib2 : ∀A.∀B.∀C.((A×B) + (A×C)) → (A×(B + C)) 
           = ΛA.ΛB.ΛC.λst:((A×B) + (A×C)).
                case st of 
                    s. ⟨@1 s, inl [C] (@2 s)⟩
                  | t. ⟨@1 t, inr [B] (@2 t)⟩
;

# 3(c)
annihil1 : ∀A.(Zero × A) → Zero
           = ΛA.λs: Zero×A. @1 s
;
annihil2 : ∀A. Zero → (Zero × A)
           = ΛA.λs: Zero. ⟨s, s [A]⟩
;


# 4(a)

# A definition of the existential quantifier in Fω
Exists :: (* ⇒ *) ⇒ *
           = λA::*=>*.∀B::*.(∀α::*.A α -> B) -> B
;

# pack_ (λα.γ) β M    ≡     pack β,M as ∃α.γ
pack_ : ∀γ::*⇒*.∀β.γ β → (∀T.(∀α.γ α→T) → T)
     = Λγ::*=>*.Λβ::*.λm:γ β.ΛT::*.λk:(∀α::*.γ α->T).k [β] m
;

# open_ [B] b [A] (Λβ.λb.e)   ≡    open b as β, b in e
open_ : ∀A::*⇒*.Exists A → Exists A 
       = ΛA::*=>*.λt:Exists A.t
;

# The signature for bools, based on an abstract type β
Bools = λβ.β×β×(β → (∀α.α → α → α));

# An implementation of the Bools signature:
bools = ⟨inr [Unit] unit,
         inl [Unit] unit,
         λb:Unit+Unit.
          Λα.
           λr:α.
            λs:α.
             case b of x.s | y.r ⟩;

# A test case for Exists
Abstract_bools = Exists Bools;

# A test case for pack_ (uncomment once you've defined pack_)
packed_bools = pack_ [Bools] [Unit+Unit] bools;

# An equivalent definition using the builtin 'pack'.
packed_bools_builtin = pack (Unit+Unit), bools as ∃β.Bools β;


# A test case for open_ (uncomment once you've defined open_)
open_example_ = λp:Exists Bools.
   open_ [Bools] p [Unit]
    (Λβ.λbools:Bools β.
       (@3 bools)
       (@1 bools)
      [Unit]
      unit unit)
 ;


# An equivalent definition using the builtin 'open':
open_example_builtin = λp:∃β.Bools β.
  open p as β, bools in
      (@3 bools)          # if
      (@1 bools)          # true
     [Unit]
     unit unit
;

# 4(b)

# The Gates signature
Gates =
  λT::*⇒*⇒*.
    (T (Bool × Bool) Bool) ×
    (∀α.T α (α×α)) ×
    (∀α.∀β.∀γ.∀δ.T α γ → T β δ → T (α × β) (γ × δ)) ×
    (∀α.∀β.∀γ.T α β → T β γ → T α γ);

# Projections from the signature.  If you have a value
#      g :: Gates G
# then the following expressions access the components of g:
#      nor [G] g
#      split [G] g
#      join [G] g
#      plug [G] g

nor : ∀G::*⇒*⇒*.Gates G →
       G (Bool×Bool) Bool =
  ΛG::*⇒*⇒*.λg:Gates G.@1 g;

split : ∀G::*⇒*⇒*.Gates G →
         (∀α.G α (α×α)) =
  ΛG::*⇒*⇒*.λg:Gates G.@2 g;

join : ∀G::*⇒*⇒*.Gates G →
        (∀α.∀β.∀γ.∀δ.G α γ → G β δ → G (α×β) (γ×δ)) =
  ΛG::*⇒*⇒*.λg:Gates G.@3 g;

plug : ∀G::*⇒*⇒*.Gates G →
        (∀α.∀β.∀γ.G α β → G β γ → G α γ) =
  ΛG::*⇒*⇒*.λg:Gates G.@4 g;

# 4(b)(i)
not : ∀G::*⇒*⇒*.Gates G → G Bool Bool
    = (ΛG::*⇒*⇒*.λg:Gates G.plug [G] g [Bool] [Bool×Bool] [Bool] (split [G] g [Bool]) (nor [G] g))
;

# 4(b)(ii)
and : ∀G::*⇒*⇒*.Gates G → G (Bool×Bool) Bool
    = ΛG::*⇒*⇒*.λg:Gates G. plug [G] g [Bool×Bool] [Bool×Bool] [Bool] (join [G] g [Bool] [Bool] [Bool] [Bool] (not [G] g) (not [G] g)) (nor [G] g)
;

# 4(b)(iii)
function_gates : Gates (λX::*.λY::*.X → Y) 
    = ⟨
        λa:(Bool×Bool).(@1 a) [Bool] tt (@2 a) [Bool] ff  tt, #nor
        Λα::*.λa:α.⟨a,a⟩, #split
        Λα::*.Λβ::*.Λγ::*.Λδ::*.λf:α->γ.λg:β->δ.λs:α×β.⟨f (@1 s),g (@2 s)⟩, #join
        Λα::*.Λβ::*.Λγ::*.λf:α->β.λg:β->γ.λa:α.g (f a)  #plug
⟩
;

# 4(b)(iv)
count_gates : Gates (λX::*.λY::*.Nat) 
    = ⟨
        succ zero, #nor
        Λα::*.zero, #split
        Λα::*.Λβ::*.Λγ::*.Λδ::*.λa:Nat.λb:Nat.add a b, #join
        Λα::*.Λβ::*.Λγ::*.λa:Nat.λb:Nat.add a b #plug
⟩
;

# 4(b)(v)
# A definition of the 2-parameter existential quantifier in Fω
Exists2 ::  ((* ⇒ * ⇒ *) ⇒ *) ⇒ *
           = λA::((* ⇒ * ⇒ *) ⇒ *).∀B::*.(∀α::(*⇒ * ⇒ *).A α -> B) -> B;

# pack2_ (λα.γ) β M    ≡     pack β,M as ∃α.γ
pack2_ :  ∀γ::((* ⇒ * ⇒ *) ⇒ *).∀β::(* ⇒ * ⇒ *).γ β → (∀T.(∀α::(* ⇒ * ⇒ *).γ α→T) → T) 
     = Λγ::((* ⇒ * ⇒ *) ⇒ *).Λβ::(* ⇒ * ⇒ *).λm:γ β.ΛT::*.λk:(∀α::(* ⇒ * ⇒ *).γ α->T).k [β] m 
;

# open2_ [B] b [A] (Λβ.λb.e)   ≡    open b as β, b in e
open2_ : ∀A::(* ⇒ * ⇒ *)⇒*.Exists2 A → Exists2 A 
       = ΛA::(* ⇒ * ⇒ *)=>*.λt:Exists2 A.t
;

# A test case for Exists2 (uncomment once you've defined Exists2):
Abstract_gates = Exists2 Gates;

# Test cases for pack2_ (uncomment once you've defined pack2_):
packed_function_gates : Exists2 Gates =
    pack2_ [Gates] [λX.λY.X → Y] function_gates;
packed_count_gates : Exists2 Gates =
    pack2_ [Gates] [λX.λY.Nat] count_gates;

# A test case for open2_ (uncomment once you've defined open2_)
opened_gates = λg:Exists2 Gates.
  open2_ [Gates] g [Unit]
   (ΛG::*=>*=>*.λg:Gates G.
     (λg:G Bool Bool.unit)
       (plug [G] g [Bool] [Bool] [Bool] (not [G] g) (not [G] g)))
;

# An equivalent definition using the builtin 'open'
opened_gates_builtin = λg:∃G::*=>*=>*. Gates G.
  open g as G, g in
    (λg:G Bool Bool.unit)
    (plug [G] g [Bool] [Bool] [Bool] (not [G] g) (not [G] g))
;
