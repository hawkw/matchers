use regex_automata::{DenseDFA, SparseDFA, StateID, DFA};
use std::{fmt, io, marker::PhantomData};

pub use regex_automata::Error;

pub struct Pattern<S = usize, A = DenseDFA<Vec<S>, S>>
where
    S: StateID,
    A: DFA<ID = S>,
{
    automaton: A,
}

pub struct Matcher<'a, S = usize, A = DenseDFA<&'a [S], S>>
where
    S: StateID,
    A: DFA<ID = S>,
{
    automaton: A,
    state: S,
    _lt: PhantomData<&'a ()>,
}

// === impl Pattern ===

impl Pattern {
    pub fn new(pattern: &str) -> Result<Self, Error> {
        let automaton = DenseDFA::new(pattern)?;
        Ok(Pattern { automaton })
    }
}

impl<S, A> Pattern<S, A>
where
    S: StateID,
    A: DFA<ID = S>,
    Self: for<'a> ToMatcher<'a, S>,
{
    #[inline]
    pub fn matches(&self, s: &impl AsRef<str>) -> bool {
        self.matcher().matches(s)
    }

    #[inline]
    pub fn debug_matches(&self, d: &impl fmt::Debug) -> bool {
        self.matcher().debug_matches(d)
    }

    #[inline]
    pub fn display_matches(&self, d: &impl fmt::Display) -> bool  {
        self.matcher().display_matches(d)
    }
}

// === impl Matcher ===

impl<'a, S, A> Matcher<'a, S, A>
where
    S: StateID,
    A: DFA<ID = S>,
{
    fn new(automaton: A) -> Self {
        let state = automaton.start_state();
        Self {
            automaton,
            state,
            _lt: PhantomData,
        }
    }

    #[inline]
    fn advance(&mut self, input: u8) {
        self.state = unsafe {
            // It's safe to call `next_state_unchecked` since the matcher may
            // only be constructed by a `Pattern`, which, in turn,can only be
            // constructed with a valid DFA.
            self.automaton.next_state_unchecked(self.state, input)
        };
    }

    #[inline]
    pub fn is_matched(&self) -> bool {
        self.automaton.is_match_state(self.state)
    }

    pub fn matches(mut self, s: &impl AsRef<str>) -> bool {
        for &byte in s.as_ref().as_bytes() {
            self.advance(byte);
            if self.automaton.is_match_or_dead_state(self.state) {
                return self.automaton.is_match_state(self.state);
            }
        }
        false
    }

    pub fn debug_matches(mut self, d: &impl fmt::Debug) -> bool {
        use std::fmt::Write;
        write!(&mut self, "{:?}", d).expect("matcher write impl should not fail");
        self.is_matched()
    }

    pub fn display_matches(mut self, d: &impl fmt::Display) -> bool {
        use std::fmt::Write;
        write!(&mut self, "{}", d).expect("matcher write impl should not fail");
        self.is_matched()
    }
}

impl<'a, S, A> fmt::Write for Matcher<'a, S, A>
where
    S: StateID,
    A: DFA<ID = S>,
{
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for &byte in s.as_bytes() {
            self.advance(byte);
            if self.automaton.is_match_or_dead_state(self.state) {
                break;
            }
        }
        Ok(())
    }
}

impl<'a, S, A> io::Write for Matcher<'a, S, A>
where
    S: StateID,
    A: DFA<ID = S>,
{
    fn write(&mut self, bytes: &[u8]) -> Result<usize, io::Error> {
        let mut i = 0;
        for &byte in bytes {
            self.advance(byte);
            i += 1;
            if self.automaton.is_match_or_dead_state(self.state) {
                break;
            }
        }
        Ok(i)
    }

    fn flush(&mut self) -> Result<(), io::Error> {
        Ok(())
    }
}

pub trait ToMatcher<'a, S>
where
    Self: crate::sealed::Sealed,
    S: StateID + 'a,
{
    type Automaton: DFA<ID = S>;
    fn matcher(&'a self) -> Matcher<'a, S, Self::Automaton,>;
}

impl<S> crate::sealed::Sealed for Pattern<S, DenseDFA<Vec<S>, S>>
where
    S: StateID,
{}

impl<'a, S> ToMatcher<'a, S> for Pattern<S, DenseDFA<Vec<S>, S>>
where
    S: StateID + 'a,
{
    type Automaton = DenseDFA<&'a [S], S>;
    fn matcher(&'a self) -> Matcher<'a, S, Self::Automaton> {
        Matcher::new(self.automaton.as_ref())
    }
}

impl<'a, S> ToMatcher<'a, S> for Pattern<S, SparseDFA<Vec<u8>, S>>
where
    S: StateID + 'a,
{
    type Automaton = SparseDFA<&'a [u8], S>;
    fn matcher(&'a self) -> Matcher<'a, S, Self::Automaton> {
        Matcher::new(self.automaton.as_ref())
    }
}

impl<S> crate::sealed::Sealed for Pattern<S, SparseDFA<Vec<u8>, S>>
where
    S: StateID,
{}

mod sealed {
    pub trait Sealed {}
}
// === DfaAsRef ===

// trait DfaAsRef<'a, S: StateID> {
//     type Ref: DFA<ID = S>;
//     fn as_dfa_ref(&'a self) -> Self::Ref;
// }

// impl<'a, T, S> DfaAsRef<'a, S> for DenseDFA<T, S>
// where
//     T: AsRef<[S]>,
//     S: StateID + 'a,
// {
//     type Ref = DenseDFA<&'a [S], S>;

//     fn as_dfa_ref(&'a self) -> Self::Ref {
//         self.as_ref()
//     }
// }

// impl<'a, T, S> DfaAsRef<'a, S> for SparseDFA<T, S>
// where
//     T: AsRef<[u8]>,
//     S: StateID + 'a,
// {
//     type Ref = SparseDFA<&'a [u8], S>;

//     fn as_dfa_ref(&'a self) -> Self::Ref {
//         self.as_ref()
//     }
// }

#[cfg(test)]
mod test {
    use super::*;

    struct HelloWorld;
    impl fmt::Debug for HelloWorld {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "hello world")
        }
    }

    #[test]
    fn debug_matches() {
        let pat = Pattern::new("hello world").unwrap();
        assert!(pat.debug_matches(&HelloWorld));

        let pat = Pattern::new("hel+o w[orl]{3}d").unwrap();
        assert!(pat.debug_matches(&HelloWorld));

        let pat = Pattern::new("goodbye world").unwrap();
        assert_eq!(pat.debug_matches(&HelloWorld), false);
    }
}
