-- Universe levels
level : Type
aref  : Type

-- Syntax

term(var) : Type

Sort : level -> term

assm : aref -> term

Pi  : level -> level -> term -> (bind term in term) -> term
lam : level -> level -> term -> (bind term in term) -> (bind term in term) -> term
app : level -> level -> term -> (bind term in term) -> term -> term -> term

Nat  : term 
zero : term 
succ : term -> term 
rec  : level -> (bind term in term) -> term -> (bind term , term in term) -> term -> term

acc    : level -> term -> (bind term , term in term) -> term -> term 
accin  : level -> term -> (bind term , term in term) -> term -> term -> term
accinv : level -> term -> (bind term , term in term) -> term -> term -> term -> term -> term
accel  : level -> level -> term -> (bind term , term in term) -> (bind term in term) -> (bind term, term in term) -> term -> term -> term

obseq  : level -> term -> term -> term -> term
cast   : level -> term -> term -> term -> term -> term
injpi1 : level -> level -> term -> term -> (bind term in term) -> (bind term in term) -> term -> term
injpi2 : level -> level -> term -> term -> (bind term in term) -> (bind term in term) -> term -> term -> term


