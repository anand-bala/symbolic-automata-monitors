# Symbolic Automata Monitors

This package provides a library for creating and manipulating symbolic automata
monitors. Initially forked from code by [Dejan
Nickovic](https://sites.google.com/view/nickovic/), and a lot of bells and whistles were
added my me.

## Alpha Status

This is purely a package that I use in my research, and haven't really documented a lot
of things, nor does this have a lot of testing. Things mostly work, but open a issue if
you do find something or send a pull request to fix it.

## Example

![An automaton for the specification "`a` and `b` need to be satisfied before `c`"](examples/specification1.tikz.png) 

The following code creates an automaton `aut` that
represents the above specification automaton:

```python
from syma import SymbolicAutomaton

aut = SymbolicAutomaton()

# Symbolic variable declarations
a = aut.declare_bool("a")
b = aut.declare_bool("b")
c = aut.declare_bool("c")

# Location definitions
aut.add_location(0, initial=True)
aut.add_location(1)
aut.add_location(2)
aut.add_location(3)
aut.add_location(4, accepting=True)

# Transition definitions
# q0
aut.add_transition(0, 0, guard=(~a & ~b))
aut.add_transition(0, 1, guard=(a & ~b))
aut.add_transition(0, 2, guard=(~a & b))
aut.add_transition(0, 3, guard=(a & b & ~c))
aut.add_transition(0, 4, guard=(a & b & c))
# q1
aut.add_transition(1, 1, guard=(~b))
aut.add_transition(1, 3, guard=(b & ~c))
aut.add_transition(1, 4, guard=(b & c))
# q2
aut.add_transition(2, 2, guard=(~a))
aut.add_transition(2, 3, guard=(a & ~c))
aut.add_transition(2, 4, guard=(a & c))
# q3
aut.add_transition(3, 3, guard=(~c))
aut.add_transition(3, 4, guard=c)
# q4
aut.add_transition(4, 4, guard=True)
```

Now, `aut` can be used to check if constraints are satisfied by some input word.
For more information, check out the documentation for [`SymbolicAutomata`][doc-symaut]
and [`Constraint`][doc-constraint].

[doc-symaut]: https://anand-bala.github.io/symbolic-automata-monitors/docs/syma.html#SymbolicAutomaton
[doc-constraint]: https://anand-bala.github.io/symbolic-automata-monitors/docs/syma.html#Constraint

To generate the above code from STL specications, run:

```shell
$ python3 ./bin/generate_symaut.py 'eventually[0,10] (x > 0)'
```

## References

- S. Jakšić, E. Bartocci, R. Grosu, and D. Ničković, “An Algebraic Framework for Runtime
  Verification,” IEEE Transactions on Computer-Aided Design of Integrated Circuits and
  Systems, vol. 37, no. 11, pp. 2233–2243, Nov. 2018, doi: 10.1109/TCAD.2018.2858460.
- M. Veanes, “Applications of Symbolic Finite Automata,” in Implementation and
  Application of Automata, vol. 7982, S. Konstantinidis, Ed. Berlin, Heidelberg:
  Springer Berlin Heidelberg, 2013, pp. 16–23. doi: 10.1007/978-3-642-39274-0_3.
- L. D’Antoni and M. Veanes, “Minimization of symbolic automata,” in Proceedings of the
  41st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages, New York,
  NY, USA, Jan. 2014, pp. 541–553. doi: 10.1145/2535838.2535849.
- L. D’Antoni and M. Veanes, “The Power of Symbolic Automata and Transducers,” in
  Computer Aided Verification, vol. 10426, R. Majumdar and V. Kunčak, Eds. Cham:
  Springer International Publishing, 2017, pp. 47–67. doi: 10.1007/978-3-319-63387-9_3.

