From Coq Require Import
     Ascii
     Basics
     Decimal
     List
     String
     ZArith.

Import ListNotations.
Local Open Scope program_scope.
Local Open Scope string_scope.

Export Coq.Strings.String.StringSyntax.

(* This makes just the [%string] key available to [Derive Show]. *)
Delimit Scope string_scope with string.

Class ShowS (A : Type) : Type := 
{
    shows : A -> (string -> string)
}.

Fixpoint shows_uint (n : uint) : (string -> string) := 
    let aux (s : string) := 
        match n with
        | Nil => s
        | D0 n => (String "0" (shows_uint n s))%string
        | D1 n => (String "1" (shows_uint n s))%string
        | D2 n => (String "2" (shows_uint n s))%string
        | D3 n => (String "3" (shows_uint n s))%string
        | D4 n => (String "4" (shows_uint n s))%string
        | D5 n => (String "5" (shows_uint n s))%string
        | D6 n => (String "6" (shows_uint n s))%string
        | D7 n => (String "7" (shows_uint n s))%string
        | D8 n => (String "8" (shows_uint n s))%string
        | D9 n => (String "9" (shows_uint n s))%string
        end in 
    aux.

Definition shows_int (n : int) : (string -> string) :=
    match n with
    | Pos n => shows_uint n
    | Neg n => (fun s : string => String "-" (shows_uint n s))
    end. 

Definition shows_nat (n : nat) : (string -> string) := 
    shows_uint (Nat.to_uint n).

Definition shows_bool (b : bool) : (string -> string) := 
    match b with 
    | true => (fun s : string => ("true" ++ s)%string)
    | false => (fun s : string => ("false" ++ s)%string)
    end.

#[global] Instance showsUint : ShowS uint := 
{|
    shows := shows_uint
|}.

#[global] Instance showsInt : ShowS int :=
{|
  shows := shows_int
|}.

#[global] Instance showsNat : ShowS nat :=
{|
  shows := shows_nat
|}.

#[global] Instance showsBool : ShowS bool :=
{|
  shows := shows_bool
|}.