Require Import Coq.Lists.List.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.
Require Import ListString.Comparison.
From Coq Require Import Arith.EqNat.


Import ListNotations.
Import C.Notations.

Definition RawString := C.t System.effect LString.t.

(** The classic Hello World program. *)
Definition hello_world (argv : list LString.t) : C.t System.effect unit :=
  System.log (LString.s "Hello world!").

Definition read_file (file_name : LString.t) : C.t System.effect LString.t :=
  let! file := System.read_file file_name in
  match file with
  | None => ret []
  | Some contents => ret contents
  end.

Definition fmap {E : Effect.t} {A B:Type}
           (f:A->B)
           (a:C.t E A) : (C.t E B) :=
  let! _a := a in ret (f _a).

Definition apply {E : Effect.t} {A B : Type}
          (f: C.t E (A -> B)) (a : C.t E A) : C.t E B :=
  let! _f := f in 
    let! _a := a in
      ret (_f _a).
  
(* check to see if b is a prefix of b *)
Fixpoint match_head (a : LString.t) (b : LString.t) : bool:=
    match a, b with
    | _, [] => true
    | [], _ => false
    | h1::t1, h2::t2 => if (Char.eqb h1 h2) then (match_head t1 t2) else false
    end.

Definition match_headS (a : RawString) (b : RawString) : C.t System.effect bool :=
  apply (fmap match_head a) b.

(* convert bool to list string *)
Definition of_bool (a:bool) :=
  if a then (LString.s "true") else (LString.s "false").

Definition _main (argv : list LString.t) : C.t System.effect unit :=
  let! content := read_file (LString.s "test/HelloWorld.txt") in
    let result := match_head content (LString.s "Hellp") in
      System.log (of_bool result).
           

Definition main := Extraction.launch _main.
Extraction "main" main.
