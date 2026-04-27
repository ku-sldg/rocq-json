From RocqJSON Require Import JSON JSON_Derive JSON_Error_Strings.
From Stdlib Require Import List.

Local Open Scope string_scope.

(* ================================================================== *)
(* Tier 1: Trivial Types, Enums, Records, and Structural Anomalies    *)
(* ================================================================== *)

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
