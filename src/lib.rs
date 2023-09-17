//! Regex matchers on character and byte streams.
//!
//! ## Overview
//!
//! The [`regex`] crate implements regular expression matching on strings and byte
//! arrays. However, in order to match the output of implementations of `fmt::Debug`
//! and `fmt::Display`, or by any code which writes to an instance of `fmt::Write`
//! or `io::Write`, it is necessary to first allocate a buffer, write to that
//! buffer, and then match the buffer against a regex.
//!
//! In cases where it is not necessary to extract substrings, but only to test whether
//! or not output matches a regex, it is not strictly necessary to allocate and
//! write this output to a buffer. This crate provides a simple interface on top of
//! the lower-level [`regex-automata`] library that implements `fmt::Write` and
//! `io::Write` for regex patterns. This may be used to test whether streaming
//! output matches a pattern without buffering that output.
//!
//! Users who need to extract substrings based on a pattern or who already have
//! buffered data should probably use the [`regex`] crate instead.
//!
//! ## Syntax
//!
//! This crate uses the same [regex syntax][syntax] of the `regex-automata` crate.
//!
//! [`regex`]: https://crates.io/crates/regex
//! [`regex-automata`]: https://crates.io/crates/regex-automata
//! [syntax]: https://docs.rs/regex-automata/0.1.7/regex_automata/#syntax

use regex_automata::Anchored;
// use regex_automata::{dense, DenseDFA, SparseDFA, StateID, DFA};
use regex_automata::dfa::{dense, sparse, StartKind};
use regex_automata::dfa::Automaton;
use regex_automata::util::primitives::StateID;
use std::{fmt, io, marker::PhantomData, str::FromStr};

/// A compiled match pattern that can match multipe inputs, or return a
/// [`Matcher`] that matches a single input.
///
/// [`Matcher`]: ../struct.Matcher.html
#[derive(Debug, Clone)]
pub struct Pattern<A = dense::DFA<Vec<u32>>>
where
    A: Automaton,
{
    automaton: A,
    start: StateID,
}

/// A reference to a [`Pattern`] that matches a single input.
///
/// [`Pattern`]: ../struct.Pattern.html
#[derive(Debug, Clone)]
pub struct Matcher<'a, A = dense::DFA<&'a [u32]>>
where
    A: Automaton,
{
    automaton: A,
    state: StateID,
    _lt: PhantomData<&'a ()>,
}

// === impl Pattern ===

impl Pattern {
    /// Returns a new `Pattern` for the given regex, or an error if the regex
    /// was invalid.
    ///
    /// The returned `Pattern` will match occurances of the pattern which start
    /// at *any* in a byte or character stream — the pattern may be preceded by
    /// any number of non-matching characters. Essentially, it will behave as
    /// though the regular expression started with a `.*?`, which enables a
    /// match to appear anywhere. If this is not the desired behavior, use
    /// [`Pattern::new_anchored`] instead.
    ///
    /// For example:
    /// ```
    /// use matchers::Pattern;
    ///
    /// // This pattern matches any number of `a`s followed by a `b`.
    /// let pattern = Pattern::new("a+b").expect("regex is not invalid");
    ///
    /// // Of course, the pattern matches an input where the entire sequence of
    /// // characters matches the pattern:
    /// assert!(pattern.display_matches(&"aaaaab"));
    ///
    /// // And, since the pattern is unanchored, it will also match the
    /// // sequence when it's followed by non-matching characters:
    /// assert!(pattern.display_matches(&"hello world! aaaaab"));
    /// ```
    pub fn new(pattern: &str) -> Result<Self, dense::BuildError> {
        let automaton = dense::DFA::new(pattern)?;
        let start = automaton.universal_start_state(Anchored::No).expect("I hope this works");
        Ok(Pattern { automaton, start })
    }

    /// Returns a new `Pattern` anchored at the beginning of the input stream,
    /// or an error if the regex was invalid.
    ///
    /// The returned `Pattern` will *only* match an occurence of the pattern in
    /// an input sequence if the first character or byte in the input matches
    /// the pattern. If this is not the desired behavior, use [`Pattern::new`]
    /// instead.
    ///
    /// For example:
    /// ```
    /// use matchers::Pattern;
    ///
    /// // This pattern matches any number of `a`s followed by a `b`.
    /// let pattern = Pattern::new_anchored("a+b")
    ///     .expect("regex is not invalid");
    ///
    /// // The pattern matches an input where the entire sequence of
    /// // characters matches the pattern:
    /// assert!(pattern.display_matches(&"aaaaab"));
    ///
    /// // Since the pattern is anchored, it will *not* match an input that
    /// // begins with non-matching characters:
    /// assert!(!pattern.display_matches(&"hello world! aaaaab"));
    ///
    /// // ...however, if we create a pattern beginning with `.*?`, it will:
    /// let pattern2 = Pattern::new_anchored(".*?a+b")
    ///     .expect("regex is not invalid");
    /// assert!(pattern2.display_matches(&"hello world! aaaaab"));
    /// ```
    pub fn new_anchored(pattern: &str) -> Result<Self, dense::BuildError> {
        let automaton = dense::Builder::new()
            .configure(dense::DFA::config().start_kind(StartKind::Anchored))
            .build(pattern)?;
        let start = automaton.universal_start_state(Anchored::Yes).expect("I hope this works");
        Ok(Pattern { automaton, start  })
    }
}

impl FromStr for Pattern {
    type Err = dense::BuildError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::new(s)
    }
}

impl<A> Pattern<A>
where
    A: Automaton,
    Self: for<'a> ToMatcher<'a>,
{
    /// Returns `true` if this pattern matches the given string.
    #[inline]
    pub fn matches(&self, s: &impl AsRef<str>) -> bool {
        self.matcher().matches(s)
    }

    /// Returns `true` if this pattern matches the formatted output of the given
    /// type implementing `fmt::Debug`.
    ///
    /// For example:
    /// ```rust
    /// use matchers::Pattern;
    ///
    /// #[derive(Debug)]
    /// pub struct Hello {
    ///     to: &'static str,
    /// }
    ///
    /// let pattern = Pattern::new(r#"Hello \{ to: "W[^"]*" \}"#).unwrap();
    ///
    /// let hello_world = Hello { to: "World" };
    /// assert!(pattern.debug_matches(&hello_world));
    ///
    /// let hello_sf = Hello { to: "San Francisco" };
    /// assert_eq!(pattern.debug_matches(&hello_sf), false);
    ///
    /// let hello_washington = Hello { to: "Washington" };
    /// assert!(pattern.debug_matches(&hello_washington));
    /// ```
    #[inline]
    pub fn debug_matches(&self, d: &impl fmt::Debug) -> bool {
        self.matcher().debug_matches(d)
    }

    /// Returns `true` if this pattern matches the formatted output of the given
    /// type implementing `fmt::Display`.
    ///
    /// For example:
    /// ```rust
    /// # use std::fmt;
    /// use matchers::Pattern;
    ///
    /// #[derive(Debug)]
    /// pub struct Hello {
    ///     to: &'static str,
    /// }
    ///
    /// impl fmt::Display for Hello {
    ///     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    ///         write!(f, "Hello {}", self.to)
    ///     }
    /// }
    ///
    /// let pattern = Pattern::new("Hello [Ww].+").unwrap();
    ///
    /// let hello_world = Hello { to: "world" };
    /// assert!(pattern.display_matches(&hello_world));
    /// assert_eq!(pattern.debug_matches(&hello_world), false);
    ///
    /// let hello_sf = Hello { to: "San Francisco" };
    /// assert_eq!(pattern.display_matches(&hello_sf), false);
    ///
    /// let hello_washington = Hello { to: "Washington" };
    /// assert!(pattern.display_matches(&hello_washington));
    /// ```
    #[inline]
    pub fn display_matches(&self, d: &impl fmt::Display) -> bool {
        self.matcher().display_matches(d)
    }

    /// Returns either a `bool` indicating whether or not this pattern matches the
    /// data read from the provided `io::Read` stream, or an `io::Error` if an
    /// error occurred reading from the stream.
    #[inline]
    pub fn read_matches(&self, io: impl io::Read) -> io::Result<bool> {
        self.matcher().read_matches(io)
    }
}

// === impl Matcher ===

impl<'a, A> Matcher<'a, A>
where
    A: Automaton,
{
    fn new(automaton: A, start_state: StateID) -> Self {
        Self {
            automaton,
            state: start_state,
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

    /// Returns `true` if this `Matcher` has matched any input that has been
    /// provided.
    #[inline]
    pub fn is_matched(&self) -> bool {
        self.automaton.is_match_state(self.automaton.next_eoi_state(self.state))
    }

    /// Returns `true` if this pattern matches the formatted output of the given
    /// type implementing `fmt::Debug`.
    pub fn matches(mut self, s: &impl AsRef<str>) -> bool {
        for &byte in s.as_ref().as_bytes() {
            self.advance(byte);
            if self.automaton.is_dead_state(self.state) {
                return false;
            }
        }
        self.is_matched()
    }

    /// Returns `true` if this pattern matches the formatted output of the given
    /// type implementing `fmt::Debug`.
    pub fn debug_matches(mut self, d: &impl fmt::Debug) -> bool {
        use std::fmt::Write;
        write!(&mut self, "{:?}", d).expect("matcher write impl should not fail");
        self.is_matched()
    }

    /// Returns `true` if this pattern matches the formatted output of the given
    /// type implementing `fmt::Display`.
    pub fn display_matches(mut self, d: &impl fmt::Display) -> bool {
        use std::fmt::Write;
        write!(&mut self, "{}", d).expect("matcher write impl should not fail");
        self.is_matched()
    }

    /// Returns either a `bool` indicating whether or not this pattern matches the
    /// data read from the provided `io::Read` stream, or an `io::Error` if an
    /// error occurred reading from the stream.
    pub fn read_matches(mut self, io: impl io::Read + Sized) -> io::Result<bool> {
        for r in io.bytes() {
            self.advance(r?);
            if self.automaton.is_dead_state(self.state) {
                return Ok(false);
            }
        }
        Ok(self.is_matched())
    }
}

impl<'a, A> fmt::Write for Matcher<'a, A>
where
    A: Automaton,
{
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for &byte in s.as_bytes() {
            self.advance(byte);
            if self.automaton.is_dead_state(self.state) {
                break;
            }
        }
        Ok(())
    }
}

impl<'a, A> io::Write for Matcher<'a, A>
where
    A: Automaton,
{
    fn write(&mut self, bytes: &[u8]) -> Result<usize, io::Error> {
        let mut i = 0;
        for &byte in bytes {
            self.advance(byte);
            i += 1;
            if self.automaton.is_dead_state(self.state) {
                break;
            }
        }
        Ok(i)
    }

    fn flush(&mut self) -> Result<(), io::Error> {
        Ok(())
    }
}

pub trait ToMatcher<'a>
where
    Self: crate::sealed::Sealed,
{
    type Automaton: Automaton;
    fn matcher(&'a self) -> Matcher<'a, Self::Automaton>;
}

impl crate::sealed::Sealed for Pattern<dense::DFA<Vec<u32>>> {}

impl<'a> ToMatcher<'a> for Pattern<dense::DFA<Vec<u32>>>
{
    type Automaton = dense::DFA<&'a [u32]>;
    fn matcher(&'a self) -> Matcher<'a, Self::Automaton> {
        Matcher::new(self.automaton.as_ref(), self.start)
    }
}

impl<'a> ToMatcher<'a> for Pattern<sparse::DFA<Vec<u8>>>
{
    type Automaton = sparse::DFA<&'a [u8]>;
    fn matcher(&'a self) -> Matcher<'a, Self::Automaton> {
        Matcher::new(self.automaton.as_ref(), self.start)
    }
}

impl crate::sealed::Sealed for Pattern<sparse::DFA<Vec<u8>>> {}

mod sealed {
    pub trait Sealed {}
}

#[cfg(test)]
mod test {
    use super::*;

    struct Str<'a>(&'a str);
    struct ReadStr<'a>(io::Cursor<&'a [u8]>);

    impl<'a> fmt::Debug for Str<'a> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    impl<'a> fmt::Display for Str<'a> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    impl<'a> io::Read for ReadStr<'a> {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            self.0.read(buf)
        }
    }

    impl Str<'static> {
        fn hello_world() -> Self {
            Self::new("hello world")
        }
    }

    impl<'a> Str<'a> {
        fn new(s: &'a str) -> Self {
            Str(s)
        }

        fn to_reader(self) -> ReadStr<'a> {
            ReadStr(io::Cursor::new(self.0.as_bytes()))
        }
    }

    fn test_debug_matches(new_pattern: impl Fn(&str) -> Result<Pattern, dense::BuildError>) {
        let pat = new_pattern("hello world").unwrap();
        assert!(pat.debug_matches(&Str::hello_world()));

        let pat = new_pattern("hel+o w[orl]{3}d").unwrap();
        assert!(pat.debug_matches(&Str::hello_world()));

        let pat = new_pattern("goodbye world").unwrap();
        assert_eq!(pat.debug_matches(&Str::hello_world()), false);
    }

    fn test_display_matches(new_pattern: impl Fn(&str) -> Result<Pattern, dense::BuildError>) {
        let pat = new_pattern("hello world").unwrap();
        assert!(pat.display_matches(&Str::hello_world()));

        let pat = new_pattern("hel+o w[orl]{3}d").unwrap();
        assert!(pat.display_matches(&Str::hello_world()));

        let pat = new_pattern("goodbye world").unwrap();
        assert_eq!(pat.display_matches(&Str::hello_world()), false);
    }

    fn test_reader_matches(new_pattern: impl Fn(&str) -> Result<Pattern, dense::BuildError>) {
        let pat = new_pattern("hello world").unwrap();
        assert!(pat
            .read_matches(Str::hello_world().to_reader())
            .expect("no io error should occur"));

        let pat = new_pattern("hel+o w[orl]{3}d").unwrap();
        assert!(pat
            .read_matches(Str::hello_world().to_reader())
            .expect("no io error should occur"));

        let pat = new_pattern("goodbye world").unwrap();
        assert_eq!(
            pat.read_matches(Str::hello_world().to_reader())
                .expect("no io error should occur"),
            false
        );
    }

    fn test_debug_rep_patterns(new_pattern: impl Fn(&str) -> Result<Pattern, dense::BuildError>) {
        let pat = new_pattern("a+b").unwrap();
        assert!(pat.debug_matches(&Str::new("ab")));
        assert!(pat.debug_matches(&Str::new("aaaab")));
        assert!(pat.debug_matches(&Str::new("aaaaaaaaaab")));
        assert_eq!(pat.debug_matches(&Str::new("b")), false);
        assert_eq!(pat.debug_matches(&Str::new("abb")), false);
        assert_eq!(pat.debug_matches(&Str::new("aaaaabb")), false);
    }

    mod anchored {
        use super::*;
        #[test]
        fn debug_matches() {
            test_debug_matches(Pattern::new_anchored)
        }

        #[test]
        fn display_matches() {
            test_display_matches(Pattern::new_anchored)
        }

        #[test]
        fn reader_matches() {
            test_reader_matches(Pattern::new_anchored)
        }

        #[test]
        fn debug_rep_patterns() {
            test_debug_rep_patterns(Pattern::new_anchored)
        }

        // === anchored behavior =============================================
        // Tests that anchored patterns match each input type only beginning at
        // the first character.
        fn test_is_anchored(f: impl Fn(&Pattern, Str) -> bool) {
            let pat = Pattern::new_anchored("a+b").unwrap();
            assert!(f(&pat, Str::new("ab")));
            assert!(f(&pat, Str::new("aaaab")));
            assert!(f(&pat, Str::new("aaaaaaaaaab")));
            assert!(!f(&pat, Str::new("bab")));
            assert!(!f(&pat, Str::new("ffab")));
            assert!(!f(&pat, Str::new("qqqqqqqaaaaab")));
        }

        #[test]
        fn debug_is_anchored() {
            test_is_anchored(|pat, input| pat.debug_matches(&input))
        }

        #[test]
        fn display_is_anchored() {
            test_is_anchored(|pat, input| pat.display_matches(&input));
        }

        #[test]
        fn reader_is_anchored() {
            test_is_anchored(|pat, input| {
                pat.read_matches(input.to_reader())
                    .expect("no io error occurs")
            });
        }

        // === explicitly unanchored =========================================
        // Tests that if an "anchored" pattern begins with `.*?`, it matches as
        // though it was unanchored.
        fn test_explicitly_unanchored(f: impl Fn(&Pattern, Str) -> bool) {
            let pat = Pattern::new_anchored(".*?a+b").unwrap();
            assert!(f(&pat, Str::new("ab")));
            assert!(f(&pat, Str::new("aaaab")));
            assert!(f(&pat, Str::new("aaaaaaaaaab")));
            assert!(f(&pat, Str::new("bab")));
            assert!(f(&pat, Str::new("ffab")));
            assert!(f(&pat, Str::new("qqqqqqqaaaaab")));
        }

        #[test]
        fn debug_explicitly_unanchored() {
            test_explicitly_unanchored(|pat, input| pat.debug_matches(&input))
        }

        #[test]
        fn display_explicitly_unanchored() {
            test_explicitly_unanchored(|pat, input| pat.display_matches(&input));
        }

        #[test]
        fn reader_explicitly_unanchored() {
            test_explicitly_unanchored(|pat, input| {
                pat.read_matches(input.to_reader())
                    .expect("no io error occurs")
            });
        }
    }

    mod unanchored {
        use super::*;
        #[test]
        fn debug_matches() {
            test_debug_matches(Pattern::new)
        }

        #[test]
        fn display_matches() {
            test_display_matches(Pattern::new)
        }

        #[test]
        fn reader_matches() {
            test_reader_matches(Pattern::new)
        }

        #[test]
        fn debug_rep_patterns() {
            test_debug_rep_patterns(Pattern::new)
        }

        // === anchored behavior =============================================
        // Tests that unanchored patterns match anywhere in the input stream.
        fn test_is_unanchored(f: impl Fn(&Pattern, Str) -> bool) {
            let pat = Pattern::new("a+b").unwrap();
            assert!(f(&pat, Str::new("ab")));
            assert!(f(&pat, Str::new("aaaab")));
            assert!(f(&pat, Str::new("aaaaaaaaaab")));
            assert!(f(&pat, Str::new("bab")));
            assert!(f(&pat, Str::new("ffab")));
            assert!(f(&pat, Str::new("qqqfqqqqaaaaab")));
        }

        #[test]
        fn debug_is_unanchored() {
            test_is_unanchored(|pat, input| pat.debug_matches(&input))
        }

        #[test]
        fn display_is_unanchored() {
            test_is_unanchored(|pat, input| pat.display_matches(&input));
        }

        #[test]
        fn reader_is_unanchored() {
            test_is_unanchored(|pat, input| {
                pat.read_matches(input.to_reader())
                    .expect("no io error occurs")
            });
        }
    }
}
