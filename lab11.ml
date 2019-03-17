(*
                             CS51 Lab 11
                              Synthesis
 *)

(* Objective:

This lab is intended to provide a review and synthesis of the first
half of the course.
 *)

(*====================================================================
Part 1. Types and type inference

......................................................................
Exercise 1. For each of the following OCaml function typings, define a
function with that name (with no explicit typing annotations, that is,
no uses of the : operator) for which OCaml would infer that
type. The functions need not be practical or do anything useful; they
need only have the requested type. For this problem, do not make use
of anything from any library modules other than
Pervasives. (The first problem is done for you as an example.)

Because our test suite merely checks the types of these functions, we
run no unit tests on the code. However, we do verify the types, so
that your code will not compile unless your answers are consistent
with the requested typings. (The stub versions we provide are already
consistent with those typings, since they type as 'a -> 'b.)
....................................................................*)

(* 1. f1 : bool -> unit *)

let f1 b = if b then () else () ;;

(* 2. f2 : int -> int option *)

let f2 x = Some (x + 0) ;;

(* 3. f3 : 'a * bool -> 'a *)

let f3 (x, b) = if b then x else x ;;

(* 4. f4 : 'a -> 'b list option *)

let f4 x = Some [] ;;

(* 5. f5: ('a -> 'b) -> ('b -> 'c) -> ('a -> 'c) *)

let f5 f g x = g (f x) ;;

(*....................................................................
Exercise 2. For each of the following top-level let definitions, give
a typing for the variable being defined that provides its most general
type (as would be inferred by OCaml) or comment it out and explain
briefly why the expression is not well typed. (The first problem is
done for you as an example.)

As with Exercise 1, because our test suite merely checks the types of
these functions, we run no unit tests on the code. However, we do
verify the types, so that your code will not compile against our
testing code unless your answers are consistent with the requested
typings.
....................................................................*)

(* 1. *)

let g x =
  x +. 42. ;;

(g : float -> float) ;;

(* 2. *)

let x = let y x = x in y ;;

(x : 'a -> 'a) ;;

(* 3. *)

let x3 = 3, 3 * 3, 3 ;;

(x3 : int * int * int) ;;

(* 4. *)

(* let x4 = List.map ((+) 3.) [4.; 5.; 6.] ;; *)

(* 5. *)

let x5 = let open List in
        fun y -> filter ((=) y) ;;

(x5 : 'a -> 'a list -> 'a list) ;;

(*====================================================================
Part 2. Defining some functions

The Pervasives.string_of_bool function returns a string representation
of a boolean. Here it is in operation:

    # string_of_bool (3 = 3) ;;
    - : string = "true"
    # string_of_bool (0 = 1) ;;
    - : string = "false"

......................................................................
Exercise 4. Provide your own definition of the function string_of_bool
(without using Pervasives.string_of_bool of course).
....................................................................*)

let string_of_bool (b : bool) : string =
  if b then "true" else "false" ;;

(*....................................................................
Exercise 3. What is the type of string_of_bool? Give it as a typing,
like

    (string_of_bool : ...) ;;
....................................................................*)

(string_of_bool : bool -> string) ;;

(* Recall that the Pervasives.compare function compares two values,
returning an int based on their relative magnitude: compare x y
returns 0 if x is equal to y, -1 if x is less than y, and +1 if x is
greater than y.

A function compare_lengths : 'a list -> 'b list -> int that compares
the lengths of two lists can be implemented using compare by taking
advantage of the length function from the List module. (For reference,
this built-in length function is, unsurprisingly, linear in the length
of its argument.):

  let compare_lengths xs ys =
    compare (List.length xs) (List.length ys) ;;

For instance,

  # compare_lengths [1] [2; 3; 4] ;;
  - : int = -1
  # compare_lengths [1; 2; 3] [4] ;;
  - : int = 1
  # compare_lengths [1; 2] [3; 4] ;;
  - : int = 0

However, this implementation of compare_lengths does a little extra
work than it needs to. Its complexity is O(n) where n is the length of
the longer of the two lists. *)

(*....................................................................
Exercise 5. Why does compare_lengths have this big-O complexity? In
particular, why does the length of the shorter list not play a part in
the complexity? We're looking for a brief informal argument here, not
a full derivation of its complexity.
....................................................................*)

(* Since length is linear in the length of its argument,
   compare_lengths is linear in the sum of the lengths of its two
   arguments. But that sum is less than or equal to twice the length
   of the longer argument. Thus, compare_lengths is in O(2n), where
   n is the length of the longer argument, hence, dropping
   multiplicative constants, O(n). *)

(*....................................................................
Exercise 6. Provide an alternative implementation of compare_lengths
whose complexity is O(n) where n is the length of the shorter of the
two lists, not the longer.
....................................................................*)

let rec compare_lengths xs ys =
  match xs, ys with
  | [], [] -> 0
  | _, [] -> 1
  | [], _ -> -1
  | _xhd :: xtl, _yhd :: ytl -> compare_lengths xtl ytl ;;

(*====================================================================
Part 3. Substitution semantics
 *)

(*....................................................................
Exercise 7. Provide a derivation demonstrating that the expression

    (fun x -> x + 2) 3

evaluates to 5 according to the substitution semantics rules in the
textbook.
....................................................................*)

(*
    fun x -> x + 2 =>
                   |  (fun x -> x + 2) => (fun x -> x + 2)
                   |  3 => 3
                   |  3 + 2 =>
                            |  3 => 3
                            |  2 => 2
                            => 5
                   => 5
 *)

(*====================================================================
Part 4. Binary search trees and Gorn addresses

In this section, you'll work with binary search trees, and learn about
a method for specifying particular nodes in trees due to computer
pioneer Saul Gorn (Figure~\ref{fig:gorn}(a)).

Binary search trees (for the purpose of this section) are binary trees
in which (non-empty) nodes store a value, and further satisfy an
invariant that for a node with value x all of the values stored in its
left subtree compare (via the < operator) as less than x and all in
the right subtree compare greater than or equal to x. This allows
efficient insertion into a tree and searching in the tree for a given
item.

Here's an algebraic data type for polymorphic binary search trees,
where the values stored at the nodes are of type 'a. *)

type 'a bintree =
  | Empty
  | Node of 'a bintree * 'a * 'a bintree ;;

(* We've provided below an attempt at a function insert : 'a -> 'a
bintree -> 'a bintree to insert a new item into a binary search
tree. Unfortunately, there are several mistakes in the code that lead
to errors, warnings, or incorrect functioning. *)

(*

1.    let insert (item : 'a) (tree : bintree) : bintree =
2.      match bintree with
3.      | Empty -> Node (Empty, item, Empty)
4.      | Node (left, old, right) ->
5.         if old < item then
6.           Node (insert item left, right)
7.         else
8.           Node (left, insert item right) ;;

*)

(*....................................................................
Exercise 8. Identify as many of these bugs as there are (but no more),
giving line numbers for each and explaining what each problem is as
succinctly but specifically as you can and describing how it might be
fixed.
....................................................................*)

(*
    1: rec keyword missing
    1: bintree should be 'a bintree (twice)
    2: bintree should be tree
    5: test is wrong parity; should be if item < old ...
    6, 8: missing middle argument (old) for Node constructor
*)

(*....................................................................
Exercise 8a. Now correct the code above for the insert function.
....................................................................*)

let rec insert (item : 'a) (tree : 'a bintree) : 'a bintree =
  match tree with
  | Empty -> Node (Empty, item, Empty)
  | Node (left, old, right) ->
     if item < old then
       Node (insert item left, old, right)
     else
       Node (left, old, insert item right) ;;

(* Using the insert function (as corrected), we can, for instance,
build a tree containing 10, 5, 15, 7, and 9, which looks like

               10
               ^
             /   \
           /       \
         /           \
        5             15
        ^              ^
      /   \          /   \
     x     7        x     x
           ^
         /   \
        x     9
              ^
            /   \
           x     x

(The x's mark the empty nodes.)

We can build this tree as follows:

    let tr = Empty
             |> insert 10
             |> insert 5
             |> insert 15
             |> insert 7
             |> insert 9 ;;

The Gorn address of a node in a tree (named after the early computer
pioneer Saul Gorn of University of Pennsylvania, who invented the
technique) is a description of the path to take from the root of the
tree to the node in question. For a binary tree, the elements of the
path specify whether to go left or right at each node starting from
the root of the tree. We'll define an enumerated type for the purpose
of recording the left/right moves. *)

type direction = Left | Right ;;

(* Thus, for the tree tr defined above, the Gorn address of the root
is [] and the Gorn address of the node containing the item 9 is [Left,
Right, Right].

......................................................................
Exercise 9. Define a function gorn : 'a -> 'a bintree -> direction
list that given a value and a binary search tree returns the Gorn
address of a node with that value in the tree. (In case of multiple
nodes with the same value, the address of any of them can be
returned.) It should raise a Failure exception if the item doesn't
occur in the tree. For instance,

    # gorn 9 tr ;;
    - : direction list = [Left; Right; Right]
    # gorn 10 tr ;;
    - : direction list = []
    # gorn 100 tr ;;
    Exception: Failure "gorn: item not found".
....................................................................*)

let rec gorn item tree =
  match tree with
  | Empty -> failwith "gorn: item not found"
  | Node (left, old, right) ->
     if item = old then []
     else if item < old then
       Left :: gorn item left
     else
       Right :: gorn item right ;;

(*....................................................................
Exercise 10. Define a function find : 'a -> 'a bintree -> bool that
given an item and a binary search tree returns true if the item is in
the tree and false otherwise. You may want to use the gorn function in
defining find. Examples of the find function in use include:

    # find 9 tr ;;
    - : bool = true
    # find 100 tr ;;
    - : bool = false
....................................................................*)

let find item tree =
  try
    let _ = gorn item tree
    in true
  with
  | Failure _ -> false ;;


(*
                              END OF LAB
*)
