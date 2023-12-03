/*
  ===============================================
  DCC831 Formal Methods
  2023.2

  Mini Project 2 - Part B

  Your name(s): Guilherme de Oliveira Silva
  ===============================================
*/

class Buffer<T(0)>
{
  //------------------------------------------
  // Abstract state
  //------------------------------------------
  // the sequence of elements in the buffer,
  // from oldest to newest
  ghost var Contents: seq<T>
  // the capacity of the buffer
  ghost var Capacity: nat

  //------------------------------------------
  // Concrete state
  //------------------------------------------
  // the elements in the buffer are stored in a
  var a: array<T>
  // position of the oldest element in the buffer
  var front: nat
  // the current number of elements in the buffer
  var size: nat

  // class invariant
  ghost predicate Valid()
    // Dafny somewhy requires both `reads this` and `reads this.a` to validate this predicate.
    reads this
    reads this.a
  {
    // concrete state invariants (to be provided)
    0 <= front < a.Length &&
    front + size < 2 * a.Length &&
    size <= a.Length &&

    // connection between abstract and concrete state
    Capacity == a.Length &&
    size == |Contents| &&
    Contents == if front + size < Capacity then a[front .. front+size]
                else a[front ..] + a[0 .. (front + size - Capacity)]
  }

  constructor init(n: int)
    requires n > 0
    ensures Contents == []
    ensures Capacity == n
    ensures Valid()
  {
    Contents := [];
    Capacity := n;
    a := new T[n];
    size := 0;
    front := 0;
  }

  function isEmpty() : bool
    reads this.a // `reads this.a` is required to use `Valid`.
    reads this
    requires Valid()
    ensures isEmpty() <==> Contents == []
  {
    size == 0
  }

  function isFull() : bool
    reads this.a // `reads this.a` is required to use `Valid`.
    reads this
    requires Valid()
    ensures isFull() <==> |Contents| == Capacity
  {
    size == a.Length
  }

  method get() returns (d: T)
    modifies this
    requires Valid()
    requires !isEmpty()
    ensures Valid()
    ensures old(Contents) == [d] + Contents
    ensures Capacity == old(Capacity)
  {
    d := a[front];

    if(front + 1 < a.Length) { front := front + 1; }
    else { front := 0; }

    size := size - 1;
    Contents := Contents[1..];
  }

  method put(d: T)
    modifies this.a
    modifies this
    requires Valid()
    requires !isFull()
    ensures Valid()
    ensures Contents == old(Contents) + [d]
    ensures Capacity == old(Capacity)
  {
    var positionToAdd : nat;

    if(front + size < a.Length) { positionToAdd := front + size; }
    else { positionToAdd := front + size - a.Length; }

    a[positionToAdd] := d;

    size := size + 1;
    Contents := Contents + [d];
  }
}
