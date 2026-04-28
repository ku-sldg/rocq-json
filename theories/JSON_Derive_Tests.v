From RocqJSON Require Import JSON JSON_Derive JSON_Error_Strings.
From Stdlib Require Import List.

Local Open Scope string_scope.

Inductive nibble :=
| x0 | x1 | x2 | x3
| x4 | x5 | x6 | x7
| x8 | x9 | xA | xB
| xC | xD | xE | xF.
Time Elpi derive.jsonifiable nibble.

Inductive nibble_plus_one :=
| y0 | y1 | y2 | y3 | y4 | y5 | y6 | y7
| y8 | y9 | yA | yB | yC | yD | yE | yF
| y10 | y11 | y12 | y13 | y14 | y15 | y16 | y17
| y18 | y19 | y1A | y1B | y1C | y1D | y1E | y1F
| y20 | y21 | y22 | y23 | y24 | y25 | y26 | y27
| y28 | y29 | y2A | y2B | y2C | y2D | y2E | y2F.
Time Elpi derive.jsonifiable nibble_plus_one.

(*
Inductive nibble_plus_two :=
| z0 | z1 | z2 | z3 | z4 | z5 | z6 | z7
| z8 | z9 | zA | zB | zC | zD | zE | zF
| z10 | z11 | z12 | z13 | z14 | z15 | z16 | z17
| z18 | z19 | z1A | z1B | z1C | z1D | z1E | z1F
| z20 | z21 | z22 | z23 | z24 | z25 | z26 | z27
| z28 | z29 | z2A | z2B | z2C | z2D | z2E | z2F
| z30 | z31 | z32 | z33 | z34 | z35 | z36 | z37
| z38 | z39 | z3A | z3B | z3C | z3D | z3E | z3F
| z40 | z41 | z42 | z43 | z44 | z45 | z46 | z47
| z48 | z49 | z4A | z4B | z4C | z4D | z4E | z4F
| z50 | z51 | z52 | z53 | z54 | z55 | z56 | z57
| z58 | z59 | z5A | z5B | z5C | z5D | z5E | z5F
| z60 | z61 | z62 | z63 | z64 | z65 | z66 | z67
| z68 | z69 | z6A | z6B | z6C | z6D | z6E | z6F.
Time Elpi derive.jsonifiable nibble_plus_two.

Inductive nibble_plus_three :=
| a00 | a01 | a02 | a03 | a04 | a05 | a06 | a07
| a08 | a09 | a0A | a0B | a0C | a0D | a0E | a0F
| a10 | a11 | a12 | a13 | a14 | a15 | a16 | a17
| a18 | a19 | a1A | a1B | a1C | a1D | a1E | a1F
| a20 | a21 | a22 | a23 | a24 | a25 | a26 | a27
| a28 | a29 | a2A | a2B | a2C | a2D | a2E | a2F
| a30 | a31 | a32 | a33 | a34 | a35 | a36 | a37
| a38 | a39 | a3A | a3B | a3C | a3D | a3E | a3F
| a40 | a41 | a42 | a43 | a44 | a45 | a46 | a47
| a48 | a49 | a4A | a4B | a4C | a4D | a4E | a4F
| a50 | a51 | a52 | a53 | a54 | a55 | a56 | a57
| a58 | a59 | a5A | a5B | a5C | a5D | a5E | a5F
| a60 | a61 | a62 | a63 | a64 | a65 | a66 | a67
| a68 | a69 | a6A | a6B | a6C | a6D | a6E | a6F
| a70 | a71 | a72 | a73 | a74 | a75 | a76 | a77
| a78 | a79 | a7A | a7B | a7C | a7D | a7E | a7F
| a80 | a81 | a82 | a83 | a84 | a85 | a86 | a87
| a88 | a89 | a8A | a8B | a8C | a8D | a8E | a8F
| a90 | a91 | a92 | a93 | a94 | a95 | a96 | a97
| a98 | a99 | a9A | a9B | a9C | a9D | a9E | a9F
| aA0 | aA1 | aA2 | aA3 | aA4 | aA5 | aA6 | aA7
| aA8 | aA9 | aAA | aAB | aAC | aAD | aAE | aAF
| aB0 | aB1 | aB2 | aB3 | aB4 | aB5 | aB6 | aB7
| aB8 | aB9 | aBA | aBB | aBC | aBD | aBE | aBF
| aC0 | aC1 | aC2 | aC3 | aC4 | aC5 | aC6 | aC7
| aC8 | aC9 | aCA | aCB | aCC | aCD | aCE | aCF
| aD0 | aD1 | aD2 | aD3 | aD4 | aD5 | aD6 | aD7
| aD8 | aD9 | aDA | aDB | aDC | aDD | aDE | aDF
| aE0 | aE1 | aE2 | aE3 | aE4 | aE5 | aE6 | aE7
| aE8 | aE9 | aEA | aEB | aEC | aED | aEE | aEF
| aF0 | aF1 | aF2 | aF3 | aF4 | aF5 | aF6 | aF7
| aF8 | aF9 | aFA | aFB | aFC | aFD | aFE | aFF.
Time Elpi derive nibble_plus_three. *)

(* ================================================================== *)
(* Tier 1: Trivial Types, Enums, Records, and Structural Anomalies    *)
(* ================================================================== *)

(* 1.0 The Empty Type *)
Inductive EmptyType : Type := .
Elpi derive.jsonifiable EmptyType.

(* 1.1. The Unit Type *)
Inductive JSONUnit : Type := 
| JsonTt.
Elpi derive.jsonifiable JSONUnit.

(* 1.2. Simple Enumeration *)
Inductive Color : Type :=
| Red
| Green
| Blue.
Elpi derive.jsonifiable Color.

(* 1.3. Single Constructor, Multiple Arguments (Tuple-like) *)
Inductive Point2D : Type :=
| MkPoint2D (x : nat) (y : nat).
Elpi derive.jsonifiable Point2D.

(* 1.4. Mixed Arity Sum Type *)
Inductive UserRole : Type :=
| Admin
| Moderator (level : nat)
| StandardUser (id : nat) (username : string)
| Guest.
Elpi derive.jsonifiable UserRole.

(* 1.5. Flat Record with primitive types *)
Record ServerConfig : Type := {
  host : string;
  port : nat;
  use_ssl : bool
}.
Elpi derive.jsonifiable ServerConfig.

(* 1.6. The Empty Record *)
Record EmptyRec : Type := {}.
Elpi derive.jsonifiable EmptyRec.

(* 1.7. Single-Field Wrapper Record *)
Record Identifier : Type := { 
  get_id : string 
}.
Elpi derive.jsonifiable Identifier.

(* 1.8. Large Enumeration (Stress testing match-case generation) *)
Inductive LogLevel : Type :=
| LTrace
| LDebug
| LInfo
| LWarn
| LError
| LFatal
| LPanic.
Elpi derive.jsonifiable LogLevel.

(* 1.9. Flat Instruction Set (Mix of no-args and primitive args) *)
Inductive Instruction : Type :=
| INop
| IPush (val : nat)
| IPop
| ILoad (reg_idx : nat)
| IStore (reg_idx : nat)
| IHalt.
Elpi derive.jsonifiable Instruction.

(* 1.10. Record Composition (Records containing other custom types) *)
Record DatabaseConfig : Type := {
  db_name : string;
  max_connections : nat
}.
Elpi derive.jsonifiable DatabaseConfig.

Record AppConfig : Type := {
  app_name : string;
  db_settings : DatabaseConfig;
  log_level : LogLevel
}.
Elpi derive.jsonifiable AppConfig.


(* ================================================================== *)
(* Tier 2: Parameterized Types, Containers, and Phantom Variables     *)
(* ================================================================== *)

(* 2.0. Single Type Parameter *)
Inductive MyOption (A : Type) : Type :=
| MySome (val : A)
| MyNone.
Elpi derive.jsonifiable MyOption.

(* 2.1. Multiple Type Parameters *)
Inductive MyResult (OkVal ErrVal : Type) : Type :=
| MyOk (val : OkVal)
| MyErr (err : ErrVal).
Elpi derive.jsonifiable MyResult.

(* 2.2. Parameterized Tuple-like Inductive *)
Inductive KeyValuePair (K V : Type) : Type :=
| MkKVP (key : K) (value : V).
Elpi derive.jsonifiable KeyValuePair.

(* 2.3. Parameterized Record *)
Record UserProfile (Meta : Type) : Type := {
  uid : nat;
  metadata : Meta;
  is_active : bool
}.
Elpi derive.jsonifiable UserProfile.

(* 2.4. Compound Parameterized Types *)
Inductive PaginatedList (A : Type) : Type :=
| Page (total_pages : nat) (current_page : nat) (items : list A).
Elpi derive.jsonifiable PaginatedList.

(* 2.5. Ternary Polymorphic Container *)
Inductive Triple (A B C : Type) : Type :=
| MkTriple (fst : A) (snd : B) (thd : C).
Elpi derive.jsonifiable Triple.

(* 2.6. Multi-parameter Sum Type *)
Inductive Either3 (A B C : Type) : Type :=
| Left3 (val : A)
| Mid3 (val : B)
| Right3 (val : C).
Elpi derive.jsonifiable Either3.

(* 2.7. Parameterized Record with Multiple Type Variables *)
Record MapEntry (K V : Type) : Type := {
  entry_key : K;
  entry_val : V;
  entry_hash : nat
}.
Elpi derive.jsonifiable MapEntry.


(* ================================================================== *)
(* Tier 3: Direct Recursion, ASTs, and Formal Methods Constructs      *)
(* ================================================================== *)

(* 3.0. Simple Linear Recursion (No Type Args) *)
Inductive MyNat : Type :=
| MyZ
| MyS (n : MyNat).
Elpi derive.jsonifiable MyNat.

(* 3.1. Parameterized Linear Recursion *)
Inductive MyList (A : Type) : Type :=
| MyNil
| MyCons (hd : A) (tl : MyList A).
Elpi derive.jsonifiable MyList.

(* 3.2. Parameterized Branching Recursion *)
Inductive BinTree (A : Type) : Type :=
| BinLeaf
| BinNode (left : BinTree A) (value : A) (right : BinTree A).
Elpi derive.jsonifiable BinTree.

(* 3.3. Complex AST-style Recursion *)
Inductive Expr : Type :=
| EConst (n : nat)
| EVar (id : string)
| EAdd (left right : Expr)
| EMul (left right : Expr)
| ELet (id : string) (bound_val : Expr) (body : Expr).
Elpi derive.jsonifiable Expr.

(* 3.4. Regular Expression AST (Extensive Branching Recursion) *)
Inductive Regex : Type :=
| REpsilon
| RChar (c : string)
| RConcat (r1 r2 : Regex)
| RUnion (r1 r2 : Regex)
| RStar (r : Regex).
Elpi derive.jsonifiable Regex.

(* 3.5. Lambda Calculus AST with De Bruijn Indices *)
Inductive DeBruijnExpr : Type :=
| DBVar (idx : nat)
| DBLam (body : DeBruijnExpr)
| DBApp (func arg : DeBruijnExpr).
Elpi derive.jsonifiable DeBruijnExpr.

(* 3.6. Monomorphic Recursion with varying argument positions *)
Inductive NatProp : Type :=
| PTrue
| PFalse
| PAnd (p1 p2 : NatProp)
| PNot (p : NatProp)
| PEq (n1 n2 : nat).
Elpi derive.jsonifiable NatProp.

(* 3.7. Parameterized Recursion with Data only at Base Cases *)
Inductive LeafTree (A : Type) : Type :=
| LLeaf (val : A)
| LNode (left right : LeafTree A).
Elpi derive.jsonifiable LeafTree.

(* 3.8. Non-uniform argument sequencing in recursion *)
Inductive LetBindingAST (A : Type) : Type :=
| LBase (val : A)
| LBind (name : string) (val : A) (rest : LetBindingAST A).
Elpi derive.jsonifiable LetBindingAST.


(* ================================================================== *)
(* Tier 4: Mutually Recursive / Unrolled Nested Edge Cases            *)
(* ================================================================== *)

Inductive nested_tree : Type :=
| NLeaf (n : nat)
| NNode (children : list (MyOption nested_tree)).
(* Unsupported nested recursive occurrence under user-defined MyOption. *)
Fail Elpi derive.jsonifiable nested_tree.

(* NOTE: These are currently failing, we don't suppport them yet!

(* 4.0. Mutually Recursive Parameterized Types (Forest / Tree approach) *)
Inductive TreeList (A : Type) : Type :=
| TNNil
| TNCons (t : MultiTree A) (ts : TreeList A)
with MultiTree (A : Type) : Type :=
| MNode (val : A) (children : TreeList A).
Elpi derive.jsonifiable TreeList.
Elpi derive.jsonifiable MultiTree.

(* 4.1. Mutually Recursive State Machine (No Args) *)
Inductive EvenState : Type :=
| EvenZero
| EvenNext (o : OddState)
with OddState : Type :=
| OddNext (e : EvenState).
Elpi derive.jsonifiable EvenState.
Elpi derive.jsonifiable OddState.

*)
