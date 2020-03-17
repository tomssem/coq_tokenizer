Require Import Coq.Lists.List.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.

Import ListNotations.
Import C.Notations.

(** The classic Hello World program. *)
Definition hello_world (argv : list LString.t) : C.t System.effect unit :=
  System.log (LString.s "Hello world!").

Definition cat (argv : list LString.t) : C.t System.effect unit :=
  match argv with
  | [_; file_name] =>
    let! content := System.read_file file_name in
    match content with
    | None => System.log (LString.s "Cannot read the file.")
    | Some content => System.log content
    end
  | _ => System.log (LString.s "Expected one parameter")
  end.

Definition main := Extraction.launch cat.
Extraction "main" main.
