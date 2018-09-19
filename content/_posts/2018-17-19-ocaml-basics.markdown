---
layout: post
title: "Adventures in OCaml Basics"
date:  08:00:00 +0200
---
[OCaml][ocaml] is a functional programming language.

There are some [tutorials] available, and we're delving today into the [basics] of OCaml.

There are two ways to run ocaml program interactively.

One is to use `ocaml`. Readline functionality can be added using `rlwrap ocaml`.

The other is to use `utop`.

To compile an ocaml program `program.ml` into a binary, use the magical command `ocamlbuild myprogram.native`.

Related Ubuntu packages include `ocaml`, `rlwrap`, `utop` and `ocamlbuild`.

The basics tutorial states the following things.

First, in interactive mode, use `;;` to specify that you're done entering every command. Why you have to do this in interactive mode but not in files is not specify.

Comments begins with `(*` and end with `*)` and can be nested.

To print a string on the screen, use

{% highlight text %}
print_endline "Hello World !"
{% endhighlight %}

To define a function, use `let f arg1 arg2 ... = `. Example:
{% highlight text %}
let double x = x + x
{% endhighlight %}

In the previous example, referring to `double` in the body would not refer to the function being defined but to any function already present in the scope.

To define a recursive function, use `let rec f arg1 arg2 ... = `. Then `f` can refers to itself when invoked in the body.

To define a local variable, use `let x = expr in body`. References to `x` in `expr` are to the `x` in the upper scope, but references to `x` in the body are to the new definition. This allows redefining variables locally.

Basic types include `int`, `float`, `bool`, `char`, `string`, `unit`, `nativeint`.

Float have double precision. There's no single precision type.

Integers are on 31 or 63 bits, native integers are on 32 or 64 bits.

Chars do not support Unicode.

To call a function `f` on arguments `arg1` `arg2`, simply write `f arg1 arg2`, i.e. no parentheseses for function calls.

To convert from one type to another, use the functions `float_of_int` where `float` is the destination and `int` is the source. Adapt accordingly to each type.

Arithmetic operators apply on integers. The versions on floats are suffixed with a dot.

OCaml performs type inference so that specifying types is almost always optional.

Also, `let` and conditionals return a value.

Here's a [meaningless example][meaningless_example] which uses many of the features described here.
{% highlight text %}
(* comment *)
(*
 * multiline
 * (* nested comment *)
 *)

let f x = int_of_float ((float_of_int x) +. 3.4)

let rec r n = 1 + if n>0 then (n + (r (n-1))) else 3

let () = let a = 7 in print_endline (string_of_int (r (let a = f a in f a)))
{% endhighlight %}

Try to identify type conversions, function definitions, recursive functions, conditionals and let which return values, variable overriding and printing strings, and make sure you're confortable with it.



[ocaml]: https://en.wikipedia.org/wiki/OCaml
[tutorials]: https://ocaml.org/learn/tutorials/ 
[basics]: https://ocaml.org/learn/tutorials/basics.html
[meaningless_example]: https://github.com/xavierdpt/adventures/tree/master/trove/ocaml/basics.ml
