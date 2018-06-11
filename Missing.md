Missing APIs from the types we cover (APIs have been added after this formalization was done)

# Cell

* Structural conversion for slices.  The matching operations in our model would be
  `&mut Cell<(A, B)>` -> `(&mut Cell<A>, &mut Cell<B>)` and
  `&Cell<(A, B)>` -> `(&Cell<A>, &Cell<B>)`.

# RefCell

* RefMut::split: https://github.com/rust-lang/rust/pull/51466
