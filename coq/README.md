Coq 8.4 is required. Here is a breakdown of the files:

| File                  | Contents
| --------------------- | ---------------------------------------------------------------
| LibTactics            | General-purpose tactics by Arthur Charguéraud.
| MyTactics             | General-purpose tactics.
| --------------------- | ---------------------------------------------------------------
| DblibTactics          | Facilities for dealing with de Bruijn indices.
| DeBruijn              |
| Environments          | Facilities for dealing with type environments.
| --------------------- | ---------------------------------------------------------------
| MyList                | A list library.
| AllocationMaps        | Definitions for functions of [0, n) to some codomain. (Used for heaps and blocks.)
| --------------------- | ---------------------------------------------------------------
| Syntax                | Monolithic syntax for mini-Rust.
| WellKindedness        | Carve several syntactic categories out of the monolithic syntax.
| Memory                | A simple memory model for mini-Rust.
| Reduction             | Operational semantics for mini-Rust.
| --------------------- | ---------------------------------------------------------------
| Types                 | Types for mini-Rust.
| --------------------- | ---------------------------------------------------------------
