From Wasm Require Import datatypes_properties.
From compcert Require Import Integers.
From parseque Require Import Parseque.
Require Import Ascii Byte.
Require Import leb128.
Require Import Coq.Arith.Le.

Definition binary_of_module (m : module) : list ascii :=
  nil.