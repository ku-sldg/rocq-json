From RocqJSON Require Import JSON JSON_Derive JSON_Error_Strings.
From Stdlib Require Import List.

Local Open Scope string_scope.

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

(* ===== Tier 5: Performant Tests ===== *)
(*
In particular, a neat test case is to look at large enumerations to stress test the match-case generation and performance of the derived JSON encoders/decoders. The following are examples of such large enumerations, with 16, 32, and 256 constructors respectively.
*)
Time Elpi derive.jsonifiable "Stdlib.btauto.Algebra.poly".

Set Default Proof Mode "Classic".

Definition Point2D_Jsonifiable' `{JN : Jsonifiable nat} : Jsonifiable Point2D.
refine (Build_Jsonifiable _ (fun p =>
  match p with
  | MkPoint2D x y =>
      JSON_Object [("MkPoint2D", JSON_Object [("x", to_JSON x); ("y", to_JSON y)])]
  end) (fun js =>
  match js with
  | JSON_Object [("MkPoint2D", JSON_Object [("x", xv); ("y", yv)])] =>
      x <- from_JSON xv ;;
      y <- from_JSON yv ;;
      res (MkPoint2D x y)
  | _ => err err_str_json_unrecognized_constructor
  end) _).
destruct a; cbn.
erewrite canonical_jsonification.
erewrite canonical_jsonification.
reflexivity.
Defined.

Definition UserRole_Jsonifiable' `{JN : Jsonifiable nat, JS : Jsonifiable string} : Jsonifiable UserRole.
refine (Build_Jsonifiable _ (fun r =>
  match r with
  | Admin => JSON_String "Admin"
  | Moderator level =>
      JSON_Object [("Moderator", JSON_Object [("level", to_JSON level)])]
  | StandardUser id username =>
      JSON_Object [("StandardUser", JSON_Object [("id", to_JSON id); ("username", to_JSON username)])]
  | Guest => JSON_String "Guest"
  end) (fun js =>
  match js with
  | JSON_String "Admin" => res Admin
  | JSON_String "Guest" => res Guest
  | JSON_Object [("Moderator", JSON_Object [("level", jlevel)])] =>
      level <- from_JSON jlevel ;;
      res (Moderator level)
  | JSON_Object [("StandardUser", JSON_Object [("id", jid); ("username", usernamev)])] =>
      id <- from_JSON jid ;;
      username <- from_JSON usernamev ;;
      res (StandardUser id username)
  | _ => err err_str_json_unrecognized_constructor
  end) _).
destruct a; cbn; 
repeat (erewrite canonical_jsonification); 
try reflexivity.
Defined.

Fixpoint bintree_to_JSON' {A : Type} `{Jsonifiable A} (t : BinTree A) : JSON :=
  match t with
  | BinLeaf _ => JSON_String "BinLeaf"
  | BinNode _ l value r =>
      JSON_Object [("BinNode", JSON_Object [
        ("left", bintree_to_JSON' l);
        ("value", to_JSON value);
        ("right", bintree_to_JSON' r)])]
  end.

Fixpoint bintree_from_JSON' {A : Type} `{Jsonifiable A} (js : JSON) : Result (BinTree A) string :=
  match js with
  | JSON_String "BinLeaf" => res (@BinLeaf A)
  | JSON_Object [("BinNode", JSON_Object [("left", jleft); ("value", jvalue); ("right", jright)])] =>
      left <- bintree_from_JSON' jleft ;;
      value <- from_JSON jvalue ;;
      right <- bintree_from_JSON' jright ;;
      res (@BinNode A left value right)
  | _ => err err_str_json_unrecognized_constructor
  end.

Definition BinTree_Jsonifiable' {A : Type} `{Jsonifiable A} : Jsonifiable (BinTree A).
refine (Build_Jsonifiable _ bintree_to_JSON' bintree_from_JSON' _).
induction a; cbn.
- reflexivity.
- rewrite IHa1.
  rewrite canonical_jsonification.
  rewrite IHa2.
  reflexivity.
Defined.

Inductive enum_16 :=
| a00 | a01 | a02 | a03 | a04 | a05 | a06 | a07
| a08 | a09 | a0A | a0B | a0C | a0D | a0E | a0F.
Time Elpi derive.jsonifiable enum_16.

Inductive enum_32 :=
| b00 | b01 | b02 | b03 | b04 | b05 | b06 | b07
| b08 | b09 | b0A | b0B | b0C | b0D | b0E | b0F
| b10 | b11 | b12 | b13 | b14 | b15 | b16 | b17
| b18 | b19 | b1A | b1B | b1C | b1D | b1E | b1F.
Time Elpi derive.jsonifiable enum_32.

Inductive enum_64 :=
| c00 | c01 | c02 | c03 | c04 | c05 | c06 | c07
| c08 | c09 | c0A | c0B | c0C | c0D | c0E | c0F
| c10 | c11 | c12 | c13 | c14 | c15 | c16 | c17
| c18 | c19 | c1A | c1B | c1C | c1D | c1E | c1F
| c20 | c21 | c22 | c23 | c24 | c25 | c26 | c27
| c28 | c29 | c2A | c2B | c2C | c2D | c2E | c2F
| c30 | c31 | c32 | c33 | c34 | c35 | c36 | c37
| c38 | c39 | c3A | c3B | c3C | c3D | c3E | c3F.
Time Elpi derive.jsonifiable enum_64.

Inductive enum_128 :=
| d00 | d01 | d02 | d03 | d04 | d05 | d06 | d07
| d08 | d09 | d0A | d0B | d0C | d0D | d0E | d0F
| d10 | d11 | d12 | d13 | d14 | d15 | d16 | d17
| d18 | d19 | d1A | d1B | d1C | d1D | d1E | d1F
| d20 | d21 | d22 | d23 | d24 | d25 | d26 | d27
| d28 | d29 | d2A | d2B | d2C | d2D | d2E | d2F
| d30 | d31 | d32 | d33 | d34 | d35 | d36 | d37
| d38 | d39 | d3A | d3B | d3C | d3D | d3E | d3F
| d40 | d41 | d42 | d43 | d44 | d45 | d46 | d47
| d48 | d49 | d4A | d4B | d4C | d4D | d4E | d4F
| d50 | d51 | d52 | d53 | d54 | d55 | d56 | d57
| d58 | d59 | d5A | d5B | d5C | d5D | d5E | d5F
| d60 | d61 | d62 | d63 | d64 | d65 | d66 | d67
| d68 | d69 | d6A | d6B | d6C | d6D | d6E | d6F.
Time Elpi derive.jsonifiable enum_128.

Inductive enum_256 :=
| e00 | e01 | e02 | e03 | e04 | e05 | e06 | e07
| e08 | e09 | e0A | e0B | e0C | e0D | e0E | e0F
| e10 | e11 | e12 | e13 | e14 | e15 | e16 | e17
| e18 | e19 | e1A | e1B | e1C | e1D | e1E | e1F
| e20 | e21 | e22 | e23 | e24 | e25 | e26 | e27
| e28 | e29 | e2A | e2B | e2C | e2D | e2E | e2F
| e30 | e31 | e32 | e33 | e34 | e35 | e36 | e37
| e38 | e39 | e3A | e3B | e3C | e3D | e3E | e3F
| e40 | e41 | e42 | e43 | e44 | e45 | e46 | e47
| e48 | e49 | e4A | e4B | e4C | e4D | e4E | e4F
| e50 | e51 | e52 | e53 | e54 | e55 | e56 | e57
| e58 | e59 | e5A | e5B | e5C | e5D | e5E | e5F
| e60 | e61 | e62 | e63 | e64 | e65 |	e66 |	e67
|	e68 |	e69 |	e6A |	e6B |	e6C |	e6D |	e6E |	e6F
|	e70 |	e71 |	e72 |	e73 |	e74 |	e75 |	e76 |	e77
|	e78 |	e79 |	e7A |	e7B	|	e7C	|	e7D	|	e7E	|	e7F
| e80 | e81 | e82 | e83 | e84 | e85 | e86 | e87
| e88 | e89 | e8A | e8B | e8C | e8D | e8E | e8F
| e90 | e91 | e92 | e93 | e94 | e95 | e96 | e97
| e98 | e99 | e9A | e9B | e9C | e9D | e9E | e9F
| eA0 | eA1 | eA2 | eA3 | eA4 | eA5 | eA6 | eA7
| eA8 | eA9 | eAA | eAB | eAC | eAD | eAE | eAF
| eB0 | eB1 | eB2 | eB3 | eB4 | eB5 | eB6 | eB7
| eB8 | eB9 | eBA | eBB | eBC | eBD | eBE | eBF
| eC0 | eC1 | eC2 | eC3 | eC4 | eC5 | eC6 | eC7
| eC8 | eC9 | eCA | eCB | eCC | eCD | eCE | eCF
| eD0 | eD1 | eD2 | eD3 | eD4 | eD5 | eD6 | eD7
| eD8 | eD9 | eDA | eDB | eDC | eDD | eDE | eDF
| eE0 | eE1 | eE2 | eE3 | eE4 | eE5 | eE6 | eE7
| eE8 | eE9 | eEA | eEB | eEC | eED | eEE | eEF
| eF0 | eF1 | eF2 | eF3 | eF4 | eF5 | eF6 | eF7
| eF8 | eF9 | eFA | eFB | eFC | eFD | eFE | eFF.
Time Elpi derive.jsonifiable enum_256.

Set Default Proof Mode "Classic".
Definition enum_256_Jsonifiable' : Jsonifiable enum_256.
Time refine (Build_Jsonifiable _ (fun e => match e with
  | e00 => JSON_String "e00" | e01 => JSON_String "e01" 
  | e02 => JSON_String "e02" | e03 => JSON_String "e03" 
  | e04 => JSON_String "e04" | e05 => JSON_String "e05" 
  | e06 => JSON_String "e06" | e07 => JSON_String "e07"
  | e08 => JSON_String "e08" | e09 => JSON_String "e09" 
  | e0A => JSON_String "e0A" | e0B => JSON_String "e0B" 
  | e0C => JSON_String "e0C" | e0D => JSON_String "e0D" 
  | e0E => JSON_String "e0E" | e0F => JSON_String "e0F"
  | e10 => JSON_String "e10" | e11 => JSON_String "e11" 
  | e12 => JSON_String "e12" | e13 => JSON_String "e13" 
  | e14 => JSON_String "e14" | e15 => JSON_String "e15" 
  | e16 => JSON_String "e16" | e17 => JSON_String "e17"
  | e18 => JSON_String "e18" | e19 => JSON_String "e19" 
  | e1A => JSON_String "e1A" | e1B => JSON_String "e1B" 
  | e1C => JSON_String "e1C" | e1D => JSON_String "e1D" 
  | e1E => JSON_String "e1E" | e1F => JSON_String "e1F"
  | e20 => JSON_String "e20" | e21 => JSON_String "e21" 
  | e22 => JSON_String "e22" | e23 => JSON_String "e23" 
  | e24 => JSON_String "e24" | e25 => JSON_String "e25" 
  | e26 => JSON_String "e26" | e27 => JSON_String "e27"
  | e28 => JSON_String "e28" | e29 => JSON_String "e29" 
  | e2A => JSON_String "e2A" | e2B => JSON_String "e2B" 
  | e2C => JSON_String "e2C" | e2D => JSON_String "e2D" 
  | e2E => JSON_String "e2E" | e2F => JSON_String "e2F"
  | e30 => JSON_String "e30" | e31 => JSON_String "e31" 
  | e32 => JSON_String "e32" | e33 => JSON_String "e33" 
  | e34 => JSON_String "e34" | e35 => JSON_String "e35" 
  | e36 => JSON_String "e36" | e37 => JSON_String "e37"
  | e38 => JSON_String "e38" | e39 => JSON_String "e39" 
  | e3A => JSON_String "e3A" | e3B => JSON_String "e3B" 
  | e3C => JSON_String "e3C" | e3D => JSON_String "e3D" 
  | e3E => JSON_String "e3E" | e3F => JSON_String "e3F"
  | e40 => JSON_String "e40" | e41 => JSON_String "e41" 
  | e42 => JSON_String "e42" | e43 => JSON_String "e43" 
  | e44 => JSON_String "e44" | e45 => JSON_String "e45" 
  | e46 => JSON_String "e46" | e47 => JSON_String "e47"
  | e48 => JSON_String "e48" | e49 => JSON_String "e49" 
  | e4A => JSON_String "e4A" | e4B => JSON_String "e4B" 
  | e4C => JSON_String "e4C" | e4D => JSON_String "e4D" 
  | e4E => JSON_String "e4E" | e4F => JSON_String "e4F"
  | e50 => JSON_String "e50" | e51 => JSON_String "e51" 
  | e52 => JSON_String "e52" | e53 => JSON_String "e53" 
  | e54 => JSON_String "e54" | e55 => JSON_String "e55" 
  | e56 => JSON_String "e56" | e57 => JSON_String "e57"
  | e58 => JSON_String "e58" | e59 => JSON_String "e59" 
  | e5A => JSON_String "e5A" | e5B => JSON_String "e5B" 
  | e5C => JSON_String "e5C" | e5D => JSON_String "e5D" 
  | e5E => JSON_String "e5E" | e5F => JSON_String "e5F"
  | e60 => JSON_String "e60" | e61 => JSON_String "e61" 
  | e62 => JSON_String "e62" | e63 => JSON_String "e63" 
  | e64 => JSON_String "e64" | e65 => JSON_String "e65" 
  | e66 => JSON_String "e66" | e67 => JSON_String "e67"
  | e68 => JSON_String "e68" | e69 => JSON_String "e69" 
  | e6A => JSON_String "e6A" | e6B => JSON_String "e6B" 
  | e6C => JSON_String "e6C" | e6D => JSON_String "e6D" 
  | e6E => JSON_String "e6E" | e6F => JSON_String "e6F"
  | e70 => JSON_String "e70" | e71 => JSON_String "e71" 
  | e72 => JSON_String "e72" | e73 => JSON_String "e73" 
  | e74 => JSON_String "e74" | e75 => JSON_String "e75" 
  | e76 => JSON_String "e76" | e77 => JSON_String "e77"
  | e78 => JSON_String "e78" | e79 => JSON_String "e79" 
  | e7A => JSON_String "e7A" | e7B => JSON_String "e7B" 
  | e7C => JSON_String "e7C" | e7D => JSON_String "e7D" 
  | e7E => JSON_String "e7E" | e7F => JSON_String "e7F"
  | e80 => JSON_String "e80" | e81 => JSON_String "e81" 
  | e82 => JSON_String "e82" | e83 => JSON_String "e83" 
  | e84 => JSON_String "e84" | e85 => JSON_String "e85" 
  | e86 => JSON_String "e86" | e87 => JSON_String "e87"
  | e88 => JSON_String "e88" | e89 => JSON_String "e89" 
  | e8A => JSON_String "e8A" | e8B => JSON_String "e8B" 
  | e8C => JSON_String "e8C" | e8D => JSON_String "e8D" 
  | e8E => JSON_String "e8E" | e8F => JSON_String "e8F"
  | e90 => JSON_String "e90" | e91 => JSON_String "e91" 
  | e92 => JSON_String "e92" | e93 => JSON_String "e93" 
  | e94 => JSON_String "e94" | e95 => JSON_String "e95" 
  | e96 => JSON_String "e96" | e97 => JSON_String "e97"
  | e98 => JSON_String "e98" | e99 => JSON_String "e99" 
  | e9A => JSON_String "e9A" | e9B => JSON_String "e9B" 
  | e9C => JSON_String "e9C" | e9D => JSON_String "e9D" 
  | e9E => JSON_String "e9E" | e9F => JSON_String "e9F"
  | eA0 => JSON_String "eA0" | eA1 => JSON_String "eA1" 
  | eA2 => JSON_String "eA2" | eA3 => JSON_String "eA3" 
  | eA4 => JSON_String "eA4" | eA5 => JSON_String "eA5" 
  | eA6 => JSON_String "eA6" | eA7 => JSON_String "eA7"
  | eA8 => JSON_String "eA8" | eA9 => JSON_String "eA9" 
  | eAA => JSON_String "eAA" | eAB => JSON_String "eAB" 
  | eAC => JSON_String "eAC" | eAD => JSON_String "eAD" 
  | eAE => JSON_String "eAE" | eAF => JSON_String "eAF"
  | eB0 => JSON_String "eB0" | eB1 => JSON_String "eB1" 
  | eB2 => JSON_String "eB2" | eB3 => JSON_String "eB3" 
  | eB4 => JSON_String "eB4" | eB5 => JSON_String "eB5" 
  | eB6 => JSON_String "eB6" | eB7 => JSON_String "eB7"
  | eB8 => JSON_String "eB8" | eB9 => JSON_String "eB9" 
  | eBA => JSON_String "eBA" | eBB => JSON_String "eBB" 
  | eBC => JSON_String "eBC" | eBD => JSON_String "eBD" 
  | eBE => JSON_String "eBE" | eBF => JSON_String "eBF"
  | eC0 => JSON_String "eC0" | eC1 => JSON_String "eC1" 
  | eC2 => JSON_String "eC2" | eC3 => JSON_String "eC3" 
  | eC4 => JSON_String "eC4" | eC5 => JSON_String "eC5" 
  | eC6 => JSON_String "eC6" | eC7 => JSON_String "eC7"
  | eC8 => JSON_String "eC8" | eC9 => JSON_String "eC9" 
  | eCA => JSON_String "eCA" | eCB => JSON_String "eCB" 
  | eCC => JSON_String "eCC" | eCD => JSON_String "eCD" 
  | eCE => JSON_String "eCE" | eCF => JSON_String "eCF"
  | eD0 => JSON_String "eD0" | eD1 => JSON_String "eD1" 
  | eD2 => JSON_String "eD2" | eD3 => JSON_String "eD3" 
  | eD4 => JSON_String "eD4" | eD5 => JSON_String "eD5" 
  | eD6 => JSON_String "eD6" | eD7 => JSON_String "eD7"
  | eD8 => JSON_String "eD8" | eD9 => JSON_String "eD9" 
  | eDA => JSON_String "eDA" | eDB => JSON_String "eDB" 
  | eDC => JSON_String "eDC" | eDD => JSON_String "eDD" 
  | eDE => JSON_String "eDE" | eDF => JSON_String "eDF"
  | eE0 => JSON_String "eE0" | eE1 => JSON_String "eE1" 
  | eE2 => JSON_String "eE2" | eE3 => JSON_String "eE3" 
  | eE4 => JSON_String "eE4" | eE5 => JSON_String "eE5" 
  | eE6 => JSON_String "eE6" | eE7 => JSON_String "eE7"
  | eE8 => JSON_String "eE8" | eE9 => JSON_String "eE9" 
  | eEA => JSON_String "eEA" | eEB => JSON_String "eEB" 
  | eEC => JSON_String "eEC" | eED => JSON_String "eED" 
  | eEE => JSON_String "eEE" | eEF => JSON_String "eEF"
  | eF0 => JSON_String "eF0" | eF1 => JSON_String "eF1" 
  | eF2 => JSON_String "eF2" | eF3 => JSON_String "eF3" 
  | eF4 => JSON_String "eF4" | eF5 => JSON_String "eF5" 
  | eF6 => JSON_String "eF6" | eF7 => JSON_String "eF7"
  | eF8 => JSON_String "eF8" | eF9 => JSON_String "eF9" 
  | eFA => JSON_String "eFA" | eFB => JSON_String "eFB" 
  | eFC => JSON_String "eFC" | eFD => JSON_String "eFD" 
  | eFE => JSON_String "eFE" | eFF => JSON_String "eFF"
  end) (fun e => 
    match e with
  | JSON_String "e00"  => res e00 | JSON_String "e01"  => res e01
  | JSON_String "e02"  => res e02 | JSON_String "e03"  => res e03
  | JSON_String "e04"  => res e04 | JSON_String "e05"  => res e05
  | JSON_String "e06"  => res e06 | JSON_String "e07" => res e07
  | JSON_String "e08"  => res e08 | JSON_String "e09"  => res e09
  | JSON_String "e0A"  => res e0A | JSON_String "e0B"  => res e0B
  | JSON_String "e0C"  => res e0C | JSON_String "e0D"  => res e0D
  | JSON_String "e0E"  => res e0E | JSON_String "e0F" => res e0F
  | JSON_String "e10"  => res e10 | JSON_String "e11"  => res e11
  | JSON_String "e12"  => res e12 | JSON_String "e13"  => res e13
  | JSON_String "e14"  => res e14 | JSON_String "e15"  => res e15
  | JSON_String "e16"  => res e16 | JSON_String "e17" => res e17
  | JSON_String "e18"  => res e18 | JSON_String "e19"  => res e19
  | JSON_String "e1A"  => res e1A | JSON_String "e1B"  => res e1B
  | JSON_String "e1C"  => res e1C | JSON_String "e1D"  => res e1D
  | JSON_String "e1E"  => res e1E | JSON_String "e1F" => res e1F
  | JSON_String "e20"  => res e20 | JSON_String "e21"  => res e21
  | JSON_String "e22"  => res e22 | JSON_String "e23"  => res e23
  | JSON_String "e24"  => res e24 | JSON_String "e25"  => res e25
  | JSON_String "e26"  => res e26 | JSON_String "e27" => res e27
  | JSON_String "e28"  => res e28 | JSON_String "e29"  => res e29
  | JSON_String "e2A"  => res e2A | JSON_String "e2B"  => res e2B
  | JSON_String "e2C"  => res e2C | JSON_String "e2D"  => res e2D
  | JSON_String "e2E"  => res e2E | JSON_String "e2F" => res e2F
  | JSON_String "e30"  => res e30 | JSON_String "e31"  => res e31
  | JSON_String "e32"  => res e32 | JSON_String "e33"  => res e33
  | JSON_String "e34"  => res e34 | JSON_String "e35"  => res e35
  | JSON_String "e36"  => res e36 | JSON_String "e37" => res e37
  | JSON_String "e38"  => res e38 | JSON_String "e39"  => res e39
  | JSON_String "e3A"  => res e3A | JSON_String "e3B"  => res e3B
  | JSON_String "e3C"  => res e3C | JSON_String "e3D"  => res e3D
  | JSON_String "e3E"  => res e3E | JSON_String "e3F" => res e3F
  | JSON_String "e40"  => res e40 | JSON_String "e41"  => res e41
  | JSON_String "e42"  => res e42 | JSON_String "e43"  => res e43
  | JSON_String "e44"  => res e44 | JSON_String "e45"  => res e45
  | JSON_String "e46"  => res e46 | JSON_String "e47" => res e47
  | JSON_String "e48"  => res e48 | JSON_String "e49"  => res e49
  | JSON_String "e4A"  => res e4A | JSON_String "e4B"  => res e4B
  | JSON_String "e4C"  => res e4C | JSON_String "e4D"  => res e4D
  | JSON_String "e4E"  => res e4E | JSON_String "e4F" => res e4F
  | JSON_String "e50"  => res e50 | JSON_String "e51"  => res e51
  | JSON_String "e52"  => res e52 | JSON_String "e53"  => res e53
  | JSON_String "e54"  => res e54 | JSON_String "e55"  => res e55
  | JSON_String "e56"  => res e56 | JSON_String "e57" => res e57
  | JSON_String "e58"  => res e58 | JSON_String "e59"  => res e59
  | JSON_String "e5A"  => res e5A | JSON_String "e5B"  => res e5B
  | JSON_String "e5C"  => res e5C | JSON_String "e5D"  => res e5D
  | JSON_String "e5E"  => res e5E | JSON_String "e5F" => res e5F
  | JSON_String "e60"  => res e60 | JSON_String "e61"  => res e61
  | JSON_String "e62"  => res e62 | JSON_String "e63"  => res e63
  | JSON_String "e64"  => res e64 | JSON_String "e65"  => res e65
  | JSON_String "e66"  => res e66 | JSON_String "e67" => res e67
  | JSON_String "e68"  => res e68 | JSON_String "e69"  => res e69
  | JSON_String "e6A"  => res e6A | JSON_String "e6B"  => res e6B
  | JSON_String "e6C"  => res e6C | JSON_String "e6D"  => res e6D
  | JSON_String "e6E"  => res e6E | JSON_String "e6F" => res e6F
  | JSON_String "e70"  => res e70 | JSON_String "e71"  => res e71
  | JSON_String "e72"  => res e72 | JSON_String "e73"  => res e73
  | JSON_String "e74"  => res e74 | JSON_String "e75"  => res e75
  | JSON_String "e76"  => res e76 | JSON_String "e77" => res e77
  | JSON_String "e78"  => res e78 | JSON_String "e79"  => res e79
  | JSON_String "e7A"  => res e7A | JSON_String "e7B"  => res e7B
  | JSON_String "e7C"  => res e7C | JSON_String "e7D"  => res e7D
  | JSON_String "e7E"  => res e7E | JSON_String "e7F" => res e7F
  | JSON_String "e80"  => res e80 | JSON_String "e81"  => res e81
  | JSON_String "e82"  => res e82 | JSON_String "e83"  => res e83
  | JSON_String "e84"  => res e84 | JSON_String "e85"  => res e85
  | JSON_String "e86"  => res e86 | JSON_String "e87" => res e87
  | JSON_String "e88"  => res e88 | JSON_String "e89"  => res e89
  | JSON_String "e8A"  => res e8A | JSON_String "e8B"  => res e8B
  | JSON_String "e8C"  => res e8C | JSON_String "e8D"  => res e8D
  | JSON_String "e8E"  => res e8E | JSON_String "e8F" => res e8F
  | JSON_String "e90"  => res e90 | JSON_String "e91"  => res e91
  | JSON_String "e92"  => res e92 | JSON_String "e93"  => res e93
  | JSON_String "e94"  => res e94 | JSON_String "e95"  => res e95
  | JSON_String "e96"  => res e96 | JSON_String "e97" => res e97
  | JSON_String "e98"  => res e98 | JSON_String "e99"  => res e99
  | JSON_String "e9A"  => res e9A | JSON_String "e9B"  => res e9B
  | JSON_String "e9C"  => res e9C | JSON_String "e9D"  => res e9D
  | JSON_String "e9E"  => res e9E | JSON_String "e9F" => res e9F
  | JSON_String "eA0"  => res eA0 | JSON_String "eA1"  => res eA1
  | JSON_String "eA2"  => res eA2 | JSON_String "eA3"  => res eA3
  | JSON_String "eA4"  => res eA4 | JSON_String "eA5"  => res eA5
  | JSON_String "eA6"  => res eA6 | JSON_String "eA7" => res eA7
  | JSON_String "eA8"  => res eA8 | JSON_String "eA9"  => res eA9
  | JSON_String "eAA"  => res eAA | JSON_String "eAB"  => res eAB
  | JSON_String "eAC"  => res eAC | JSON_String "eAD"  => res eAD
  | JSON_String "eAE"  => res eAE | JSON_String "eAF" => res eAF
  | JSON_String "eB0"  => res eB0 | JSON_String "eB1"  => res eB1
  | JSON_String "eB2"  => res eB2 | JSON_String "eB3"  => res eB3
  | JSON_String "eB4"  => res eB4 | JSON_String "eB5"  => res eB5
  | JSON_String "eB6"  => res eB6 | JSON_String "eB7" => res eB7
  | JSON_String "eB8"  => res eB8 | JSON_String "eB9"  => res eB9
  | JSON_String "eBA"  => res eBA | JSON_String "eBB"  => res eBB
  | JSON_String "eBC"  => res eBC | JSON_String "eBD"  => res eBD
  | JSON_String "eBE"  => res eBE | JSON_String "eBF" => res eBF
  | JSON_String "eC0"  => res eC0 | JSON_String "eC1"  => res eC1
  | JSON_String "eC2"  => res eC2 | JSON_String "eC3"  => res eC3
  | JSON_String "eC4"  => res eC4 | JSON_String "eC5"  => res eC5
  | JSON_String "eC6"  => res eC6 | JSON_String "eC7" => res eC7
  | JSON_String "eC8"  => res eC8 | JSON_String "eC9"  => res eC9
  | JSON_String "eCA"  => res eCA | JSON_String "eCB"  => res eCB
  | JSON_String "eCC"  => res eCC | JSON_String "eCD"  => res eCD
  | JSON_String "eCE"  => res eCE | JSON_String "eCF" => res eCF
  | JSON_String "eD0"  => res eD0 | JSON_String "eD1"  => res eD1
  | JSON_String "eD2"  => res eD2 | JSON_String "eD3"  => res eD3
  | JSON_String "eD4"  => res eD4 | JSON_String "eD5"  => res eD5
  | JSON_String "eD6"  => res eD6 | JSON_String "eD7" => res eD7
  | JSON_String "eD8"  => res eD8 | JSON_String "eD9"  => res eD9
  | JSON_String "eDA"  => res eDA | JSON_String "eDB"  => res eDB
  | JSON_String "eDC"  => res eDC | JSON_String "eDD"  => res eDD
  | JSON_String "eDE"  => res eDE | JSON_String "eDF" => res eDF
  | JSON_String "eE0"  => res eE0 | JSON_String "eE1"  => res eE1
  | JSON_String "eE2"  => res eE2 | JSON_String "eE3"  => res eE3
  | JSON_String "eE4"  => res eE4 | JSON_String "eE5"  => res eE5
  | JSON_String "eE6"  => res eE6 | JSON_String "eE7" => res eE7
  | JSON_String "eE8"  => res eE8 | JSON_String "eE9"  => res eE9
  | JSON_String "eEA"  => res eEA | JSON_String "eEB"  => res eEB
  | JSON_String "eEC"  => res eEC | JSON_String "eED"  => res eED
  | JSON_String "eEE"  => res eEE | JSON_String "eEF" => res eEF
  | JSON_String "eF0"  => res eF0 | JSON_String "eF1"  => res eF1
  | JSON_String "eF2"  => res eF2 | JSON_String "eF3"  => res eF3
  | JSON_String "eF4"  => res eF4 | JSON_String "eF5"  => res eF5
  | JSON_String "eF6"  => res eF6 | JSON_String "eF7" => res eF7
  | JSON_String "eF8"  => res eF8 | JSON_String "eF9"  => res eF9
  | JSON_String "eFA"  => res eFA | JSON_String "eFB"  => res eFB
  | JSON_String "eFC"  => res eFC | JSON_String "eFD"  => res eFD
  | JSON_String "eFE"  => res eFE | JSON_String "eFF" => res eFF
  | _ => err err_str_json_unrecognized_constructor
  end
  ) _); destruct a; reflexivity.
Qed.

From Corelib Require Import Extraction.

Extraction "enum_256.ml" enum_256_Jsonifiable.
Extraction "enum_256_2.ml" enum_256_Jsonifiable'.
Extraction "jsonifiable_suite.ml"
  Point2D_Jsonifiable Point2D_Jsonifiable'
  UserRole_Jsonifiable UserRole_Jsonifiable'
  BinTree_Jsonifiable BinTree_Jsonifiable'.
