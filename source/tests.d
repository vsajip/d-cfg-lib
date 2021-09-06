module tests;

import std.algorithm.iteration;
import std.complex;
import std.conv;
import std.datetime;
import std.datetime.systime;
import std.datetime.timezone;
import std.format;
import std.path;
import std.range;
import std.regex;
import std.stdio;
import std.string;
import std.typecons;
import std.utf;
import std.variant;

import dunit;

import config;

void assertIn(string s1, string s2, lazy string msg = null,
              string file = __FILE__, size_t line = __LINE__)
{
    if (s2.indexOf(s1) >= 0) {
        return;
    }
    string message = (msg !is null) ? msg : format!"'%s' not found in '%s'"(s1, s2);
    fail(message, file, line);
}

class BaseTest {
    static auto SEPARATOR_PATTERN = regex("^-- ([A-Z]\\d+) -+");

    public string[string] loadData(string filename) {
        string[string] result;
        auto key = "";
        string[] lines = new string[0];

        auto f = File(filename, "r");
        foreach(line; f.byLine()) {
            auto m = line.matchFirst(SEPARATOR_PATTERN);

            if (m.empty) {
                lines ~= to!string(line);
            }
            else {
                if ((key != "") && (lines.length > 0)) {
                    result[key] = lines.join("\n");
                }
                key = to!string(m[1]);
                lines = new string[0];
            }
        }
        f.close();
        return result;
    }

    public ASTNode[string] toMap(MappingNode node) {
        ASTNode[string] result;

        foreach(kvp; node.elements) {
            auto key = (cast(Token) kvp.key).value.toString();

            result[key] = kvp.value;
        }
        return result;
    }

    Token W(string s) {
        Variant v = null;

        return new Token(TokenKind.Word, s, v);
    }

    Token S(string s, string val) {
        Variant v = val;

        return new Token(TokenKind.String, s, v);
    }

    Token N(long n) {
        Variant v = n;

        return new Token(TokenKind.Integer, format!"%d"(n), v);
    }

    SliceNode SN(ASTNode start, ASTNode stop, ASTNode step) {
        return new SliceNode(start, stop, step);
    }

    void compareObjects(Object e, Object a, Object context=null) {
        if ((e is null) && (a is null)) {
            return;
        }
        auto equal = (e !is null) && (a !is null);
        if (equal) {
            equal = typeid(e) == typeid(a);
        }
        if (equal) {
            if (typeid(e) == typeid(Object[])) {
                //auto ea =  cast(Object[])e;
                //auto aa = cast(Object[]) a;
                //compareArrays(ea, aa);
            }
            else if (typeid(e) == typeid(UnaryNode)) {
                auto en = cast(UnaryNode) e;
                auto an = cast(UnaryNode) a;

                assertEquals(en.kind, an.kind);
                compareObjects(en.operand, an.operand);
            }
            else if (typeid(e) == typeid(BinaryNode)) {
                    auto en = cast(BinaryNode) e;
                    auto an = cast(BinaryNode) a;

                    assertEquals(en.kind, an.kind);
                    compareObjects(en.left, an.left);
                    compareObjects(en.right, an.right);
            }
            else if (typeid(e) == typeid(SliceNode)) {
                auto en = cast(SliceNode) e;
                auto an = cast(SliceNode) a;

                assertEquals(en.kind, an.kind);
                compareObjects(en.start, an.start);
                compareObjects(en.stop, an.stop);
                compareObjects(en.step, an.step);
            }
            else if (typeid(e) == typeid(Token)) {
                auto et = cast(Token) e;
                auto at = cast(Token) a;

                assertEquals(et.kind, at.kind);
                assertEquals(et.text, at.text);
                assertEquals(et.value, at.value);
            }
        }
        if (!equal) {
            auto s = (context is null) ? "" : format!" (%s)"(context);
            auto msg = format!"Failed%s: expected %s, actual %s"(s, e, a);
        }
    }

    void compareArrays(Object[] e, Object[] a) {
        assertEquals(e.length, a.length);
        for (auto i = 0; i < e.length; i++) {
            compareObjects(e[i], a[i]);
        }
    }

    string dataFilePath(string[] s...) {
        s.insertInPlace(0, "resources");
        return buildPath(s);
    }
}

class TokenizerTests : BaseTest {

    mixin UnitTest;

    @Test
    public void location()
    {
        Location loc = new Location();

        assertEquals(1, loc.line);
        assertEquals(1, loc.column);

        loc.nextLine();

        assertEquals(2, loc.line);
        assertEquals(1, loc.column);
    }

    @Test
    public void decoding() {
        auto f = File(dataFilePath("all_unicode.bin"));
        auto r = inputRangeObject(f.byChunk(8192).joiner);
        auto d = new Decoder(r);
        auto i = 0;

        for (i = 0; i < 0xD800; i++) {
            auto c = d.decode();

            assertEquals(i, cast(int) c);
        }
        for (i = 0xE000; i < 0x110000; i++) {
            auto c = d.decode();

            assertEquals(i, cast(int) c);
        }
    }

    @Test
    public void decoding_edge_cases() {
        ubyte[] invalid = new ubyte[1];

        invalid[0] = 195;
        auto r = inputRangeObject(invalid);
        auto d = new Decoder(r);

        auto e = expectThrows(d.decode());
        assertEquals(e.msg, "Decoding error");
    }

    @Test
    public void locations() {
        alias Position = Tuple!(int, "sline", int, "scol", int, "eline", int, "ecol");

        Position[] positions = new Position[0];

        auto f = File(dataFilePath("pos.forms.cfg.txt"), "r");
        foreach (line; f.byLine()) {
            auto parts = line.split().map!(s => to!int(s));

            positions ~= Position(parts[0], parts[1], parts[2], parts[3]);
        }
        f.close();
        f = File(dataFilePath("forms.cfg"));
        auto r = inputRangeObject(f.byChunk(8192).joiner);
        auto tokenizer = new Tokenizer(r);
        foreach (i, position; positions.enumerate()) {
            auto token = tokenizer.getToken();
            //if (i == 3455) {
            //    writeln("about to fail");
            //}
            assertEquals(position.sline, token.start.line);
            assertEquals(position.scol, token.start.column);
            assertEquals(position.eline, token.end.line);
            assertEquals(position.ecol, token.end.column);
        }
    }

    private Tokenizer makeTokenizer(string s) {
        auto r = inputRangeObject(s.representation.map!(b => ubyte(b)));

        return new Tokenizer(r);
    }

    void compareLocations(Location e, Location a) {
        assertEquals(e.line, a.line);
        assertEquals(e.column, a.column);
    }

    @Test
    public void tokens() {
        auto tokenizer = makeTokenizer("");

        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer("# a comment\n");
        auto token = tokenizer.getToken();
        assertEquals(TokenKind.Newline, token.kind);
        assertEquals(token.text, "# a comment");
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer("foo");
        token = tokenizer.getToken();
        assertEquals(TokenKind.Word, token.kind);
        assertEquals("foo", token.text);
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer("'foo'");
        token = tokenizer.getToken();
        assertEquals(TokenKind.String, token.kind);
        assertEquals("'foo'", token.text);
        assertEquals("foo", token.value.get!string);
        compareLocations(new Location(1, 1), token.start);
        compareLocations(new Location(1, 5), token.end);
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer("2.71828");
        token = tokenizer.getToken();
        assertEquals(TokenKind.Float, token.kind);
        assertEquals("2.71828", token.text);
        assertEquals(2.71828, token.value.get!(double));
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer(".5");
        token = tokenizer.getToken();
        assertEquals(TokenKind.Float, token.kind);
        assertEquals(".5", token.text);
        assertEquals(0.5, token.value.get!(double));
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer("-.5");
        token = tokenizer.getToken();
        assertEquals(TokenKind.Float, token.kind);
        assertEquals("-.5", token.text);
        assertEquals(-0.5, token.value.get!(double));
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer("0x123aBc");
        token = tokenizer.getToken();
        assertEquals(TokenKind.Integer, token.kind);
        assertEquals("0x123aBc", token.text);
        assertEquals(0x123abcL, token.value);
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer("0o123");
        token = tokenizer.getToken();
        assertEquals(TokenKind.Integer, token.kind);
        assertEquals("0o123", token.text);
        assertEquals(83L, token.value);
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer("0123");
        token = tokenizer.getToken();
        assertEquals(TokenKind.Integer, token.kind);
        assertEquals("0123", token.text);
        assertEquals(83L, token.value);
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer("0b0001_0110_0111");
        token = tokenizer.getToken();
        assertEquals(TokenKind.Integer, token.kind);
        assertEquals("0b0001_0110_0111", token.text);
        assertEquals(0x167L, token.value);
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer("-4");
        token = tokenizer.getToken();
        assertEquals(TokenKind.Integer, token.kind);
        assertEquals("-4", token.text);
        assertEquals(-4L, token.value);
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer("-4e8");
        token = tokenizer.getToken();
        assertEquals(TokenKind.Float, token.kind);
        assertEquals("-4e8", token.text);
        assertEquals(-4e8, token.value.get!(double));
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer("1e8");
        token = tokenizer.getToken();
        assertEquals(TokenKind.Float, token.kind);
        assertEquals("1e8", token.text);
        assertEquals(1e8, token.value.get!(double));
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer("1e-8");
        token = tokenizer.getToken();
        assertEquals(TokenKind.Float, token.kind);
        assertEquals("1e-8", token.text);
        assertEquals(1e-8, token.value.get!(double));
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        tokenizer = makeTokenizer("4.3j");
        token = tokenizer.getToken();
        assertEquals(TokenKind.Complex, token.kind);
        assertEquals("4.3j", token.text);
        assertEquals(complex(0.0, 4.3), token.value.get!(Complex!double));
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);
        alias Empty = Tuple!(string, "source", int, "line", int, "column");

        auto empties = [
            Empty("''", 1, 2),
            Empty("\"\"", 1, 2),
            Empty("''''''", 1, 6),
            Empty("\"\"\"\"\"\"", 1, 6)
        ];

        foreach (empty; empties) {
            tokenizer = makeTokenizer(empty.source);
            token = tokenizer.getToken();
            assertEquals(TokenKind.String, token.kind);
            assertEquals(empty.source, token.text);
            assertEquals("", token.value.get!(string));
            compareLocations(new Location(empty.line, empty.column), token.end);
            assertEquals(TokenKind.EOF, tokenizer.getToken().kind);
        }

        auto s = "\"\"\"abc\ndef\n\"\"\"";
        tokenizer = makeTokenizer(s);
        token = tokenizer.getToken();
        assertEquals(TokenKind.String, token.kind);
        assertEquals(s, token.text);
        assertEquals("abc\ndef\n", token.value.get!(string));
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        s = "'\\n'";
        tokenizer = makeTokenizer(s);
        token = tokenizer.getToken();
        assertEquals(TokenKind.String, token.kind);
        assertEquals(s, token.text);
        assertEquals("\n", token.value.get!(string));
        assertEquals(TokenKind.EOF, tokenizer.getToken().kind);

        auto punct = "< > { } [ ] ( ) + - * / ** // % . <= <> << >= >> == != , : @ ~ & | ^ $ && ||";

        tokenizer = makeTokenizer(punct);
        auto parts = split(punct);

        parts ~= "";

        auto expectedKinds = [
            TokenKind.LessThan, TokenKind.GreaterThan, TokenKind.LeftCurly, TokenKind.RightCurly,
            TokenKind.LeftBracket, TokenKind.RightBracket, TokenKind.LeftParenthesis, TokenKind.RightParenthesis,
            TokenKind.Plus, TokenKind.Minus, TokenKind.Star, TokenKind.Slash, TokenKind.Power, TokenKind.SlashSlash,
            TokenKind.Modulo, TokenKind.Dot, TokenKind.LessThanOrEqual, TokenKind.AltUnequal, TokenKind.LeftShift,
            TokenKind.GreaterThanOrEqual, TokenKind.RightShift, TokenKind.Equal, TokenKind.Unequal, TokenKind.Comma,
            TokenKind.Colon, TokenKind.At, TokenKind.BitwiseComplement, TokenKind.BitwiseAnd, TokenKind.BitwiseOr,
            TokenKind.BitwiseXor, TokenKind.Dollar, TokenKind.And, TokenKind.Or,
            TokenKind.EOF
        ];
        assertEquals(parts.length, expectedKinds.length);
        for (auto i = 0; i < parts.length; i++) {
            token = tokenizer.getToken();

            assertEquals(parts[i], token.text);
            assertEquals(expectedKinds[i], token.kind);
        }

        auto keywords = "true false null is in not and or";
        tokenizer = makeTokenizer(keywords);
        parts = split(keywords);
        parts ~= "";
        expectedKinds = [
            TokenKind.True, TokenKind.False, TokenKind.None, TokenKind.Is,
            TokenKind.In, TokenKind.Not, TokenKind.And, TokenKind.Or,
            TokenKind.EOF
        ];
        assertEquals(parts.length, expectedKinds.length);
        for (auto i = 0; i < parts.length; i++) {
            token = tokenizer.getToken();

            assertEquals(parts[i], token.text);
            assertEquals(expectedKinds[i], token.kind);
            switch (token.kind) {
            case TokenKind.False:
                assertFalse(token.value.get!(bool));
                break;
            case TokenKind.True:
                assertTrue(token.value.get!(bool));
                break;
            case TokenKind.None:
                assertEquals(NullValue, token.value.get!(immutable(Object)));
                break;
            default:
                break;
            }
        }

        auto newlines = "\n \r \r\n";
        tokenizer = makeTokenizer(newlines);
        for (auto i = 0; i < 4; i++) {
            token = tokenizer.getToken();
            auto expected = (i < 3) ? TokenKind.Newline : TokenKind.EOF;
            assertEquals(expected, token.kind);
        }
    }

    @Test
    public void badTokens() {
        alias Case = Tuple!(string, "source", string, "message", int, "line", int, "column");

        auto badNumbers = [
            Case("9a", "invalid character in number", 1, 2),
            Case("079", "invalid character in number", 1, 1),
            Case("0xaBcz", "invalid character in number", 1, 6),
            Case("0o79", "invalid character in number", 1, 4),
            Case(".5z", "invalid character in number", 1, 3),
            Case("0.5.7", "invalid character in number", 1, 4),
            Case(" 0.4e-z", "invalid character in number", 1, 7),
            Case(" 0.4e-8.3", "invalid character in number", 1, 8),
            Case(" 089z", "invalid character in number", 1, 5),
            Case("0o89z", "invalid character in number", 1, 3),
            Case("0X89g", "invalid character in number", 1, 5),
            Case("10z", "invalid character in number", 1, 3),
            Case("0.4e-8Z", "invalid character in number", 1, 7),
            Case("123_", "invalid '_' at end of number: 123_", 1, 4),
            Case("1__23", "invalid '_' in number: 1__", 1, 3),
            Case("1_2__3", "invalid '_' in number: 1_2__", 1, 5),
            Case("0.4e-8_", "invalid '_' at end of number: 0.4e-8_", 1, 7),
            Case("0.4_e-8", "invalid '_' at end of number: 0.4_", 1, 4),
            Case("0._4e08", "invalid '_' in number: 0._", 1, 3),
            Case("\\ ", "unexpected character: \\", 1, 2)
        ];

        foreach (c; badNumbers) {
            auto tokenizer = makeTokenizer(c.source);
            auto e = expectThrows(tokenizer.getToken());
            assertIn(c.message, e.msg);
            compareLocations(new Location(c.line, c.column), (cast(TokenizerException) e).location);
        }

        auto badStrings = [
            Case("\'", "unterminated string:",1, 1),
            Case("\"", "unterminated string:",1, 1),
            Case("\'\'\'", "unterminated string:", 1, 1),
            Case("  ;", "unexpected character: ", 1, 3)
        ];

        foreach (c; badStrings) {
            auto tokenizer = makeTokenizer(c.source);
            auto msg = format!"Failed for '%s'"(c.source);
            auto e = expectThrows(tokenizer.getToken(), msg);

            assertIn(c.message, e.msg);
            compareLocations(new Location(c.line, c.column), (cast(TokenizerException) e).location);
        }
    }

    @Test
    public void escapes() {
        alias Case = Tuple!(string, "source", string, "result");

        auto cases = [
            Case("'\\a'", "\u0007"),
            Case("'\\b'", "\b"),
            Case("'\\f'", "\u000C"),
            Case("'\\n'", "\n"),
            Case("'\\r'", "\r"),
            Case("'\\t'", "\t"),
            Case("'\\v'", "\u000B"),
            Case("'\\\\'", "\\"),
            Case("'\\''", "'"),
            Case("'\\\"'", "\""),
            Case("'\\xAB'", "\u00AB"),
            Case("'\\u2803'", "\u2803"),
            Case("'\\u28A0abc\\u28A0'", "\u28a0abc\u28a0"),
            Case("'\\u28A0abc'", "\u28a0abc"),
            Case("'\\uE000'", "\ue000"),
            Case("'\\U0010ffff'", "\U0010ffff")
        ];

        foreach (c; cases) {
            auto tokenizer = makeTokenizer(c.source);
            auto token = tokenizer.getToken();
            assertEquals(TokenKind.String, token.kind);
            assertEquals(c.source, token.text);
            assertEquals(c.result, token.value.get!(string));
            assertEquals(TokenKind.EOF, tokenizer.getToken().kind);
        }

        auto badCases = [
            "'\\z'",
            "'\\x'",
            "'\\xa'",
            "'\\xaz'",
            "'\\u'",
            "'\\u0'",
            "'\\u01'",
            "'\\u012'",
            "'\\u012z'",
            "'\\u012zA'",
            "'\\ud800'",
            "'\\udfff'",
            "'\\U00110000'"
        ];

        foreach (s; badCases) {
            auto tokenizer = makeTokenizer(s);
            auto e = expectThrows(tokenizer.getToken());
            assertIn("invalid escape sequence", e.msg);
        }
    }

    @Test
    public void data() {
        auto info = loadData(dataFilePath("testdata.txt"));
    }
}

class ParserTests : BaseTest {
    mixin UnitTest;

    private Parser makeParser(string s) {
        auto r = inputRangeObject(s.representation.map!(b => ubyte(b)));

        return new Parser(r);
    }

    @Test
    public void simpleFragments() {
        auto p = makeParser("a + 4");
        auto node = cast(BinaryNode) p.expr();

        assertTrue(p.atEnd);
        assertEquals(TokenKind.Plus, node.kind);
        assertEquals(TokenKind.Word, node.left.kind);
        assertEquals("a", (cast(Token) node.left).text);
        assertEquals(TokenKind.Integer, node.right.kind);
        assertEquals(4L, (cast(Token) node.right).value.get!(long));

        p = makeParser("a.b.c.d");
        node = cast(BinaryNode) p.expr();

        assertTrue(p.atEnd);
        assertEquals(TokenKind.Dot, node.kind);
        assertEquals(TokenKind.Word, node.right.kind);
        assertEquals("d", (cast(Token) node.right).text);
        node = cast(BinaryNode) node.left;
        assertEquals(TokenKind.Dot, node.kind);
        assertEquals(TokenKind.Word, node.right.kind);
        assertEquals("c", (cast(Token) node.right).text);
        node = cast(BinaryNode) node.left;
        assertEquals(TokenKind.Dot, node.kind);
        assertEquals(TokenKind.Word, node.left.kind);
        assertEquals("a", (cast(Token) node.left).text);
        assertEquals(TokenKind.Word, node.right.kind);
        assertEquals("b", (cast(Token) node.right).text);
    }

    @Test
    public void slices() {
        auto p = makeParser("foo[start:stop:step]");
        auto node = cast(BinaryNode) p.expr();
        auto expected = new BinaryNode(TokenKind.Colon, W("foo"), SN(W("start"), W("stop"), W("step")));

        compareObjects(expected, node);

        p = makeParser("foo[start:stop]");
        node = cast(BinaryNode) p.expr();

        expected = new BinaryNode(TokenKind.Colon, W("foo"), SN(W("start"), W("stop"), null));
        compareObjects(expected, node);

        p = makeParser("foo[start:stop:]");
        node = cast(BinaryNode) p.expr();

        expected = new BinaryNode(TokenKind.Colon, W("foo"), SN(W("start"), W("stop"), null));
        compareObjects(expected, node);

        p = makeParser("foo[start:]");
        node = cast(BinaryNode) p.expr();

        expected = new BinaryNode(TokenKind.Colon, W("foo"), SN(W("start"), null, null));
        compareObjects(expected, node);

        p = makeParser("foo[:stop]");
        node = cast(BinaryNode) p.expr();

        expected = new BinaryNode(TokenKind.Colon, W("foo"), SN(null, W("stop"), null));
        compareObjects(expected, node);

        p = makeParser("foo[:stop:]");
        node = cast(BinaryNode) p.expr();

        expected = new BinaryNode(TokenKind.Colon, W("foo"), SN(null, W("stop"), null));
        compareObjects(expected, node);

        p = makeParser("foo[::step]");
        node = cast(BinaryNode) p.expr();

        expected = new BinaryNode(TokenKind.Colon, W("foo"), SN(null, null, W("step")));
        compareObjects(expected, node);

        p = makeParser("foo[::]");
        node = cast(BinaryNode) p.expr();

        expected = new BinaryNode(TokenKind.Colon, W("foo"), SN(null, null, null));
        compareObjects(expected, node);

        p = makeParser("foo[:]");
        node = cast(BinaryNode) p.expr();

        expected = new BinaryNode(TokenKind.Colon, W("foo"), SN(null, null, null));
        compareObjects(expected, node);

        p = makeParser("foo[start::]");
        node = cast(BinaryNode) p.expr();

        expected = new BinaryNode(TokenKind.Colon, W("foo"), SN(W("start"), null, null));
        compareObjects(expected, node);

        p = makeParser("foo[start::step]");
        node = cast(BinaryNode) p.expr();

        expected = new BinaryNode(TokenKind.Colon, W("foo"), SN(W("start"), null, W("step")));
        compareObjects(expected, node);
    }

    @Test
    public void data() {
        auto info = loadData(dataFilePath("testdata.txt"));
        auto messages = [
            "D01": "unexpected type for key: Integer",
            "D02": "unexpected type for key: LeftBracket",
            "D03": "unexpected type for key: LeftCurly"
        ];

        foreach(k, v; info) {
            auto p = makeParser(v);

            if (k < "D01") {
                auto node = cast(MappingNode) p.mappingBody();

                assertTrue(p.atEnd);
            }
            else {
                auto e = expectThrows(p.mappingBody());

                assertIn(messages[k], e.msg);
            }
        }
    }

    @Test
    public void json() {
        auto f = File(dataFilePath("forms.conf"));
        auto r = inputRangeObject(f.byChunk(8192).joiner);
        auto p = new Parser(r);
        auto node = cast(MappingNode) p.mapping();
        auto d = toMap(node);

        assertTrue("refs" in d);
        assertTrue("fieldsets" in d);
        assertTrue("forms" in d);
        assertTrue("modals" in d);
        assertTrue("pages" in d);
    }
}

Variant VS(string s) {
    Variant v = s;

    return v;
}

Variant VN(long n) {
    Variant v = n;

    return v;
}

Variant VB(bool b) {
    Variant v = b;

    return v;
}

Variant VL(Variant[] list) {
    Variant result = list;

    return result;
}

Variant VM(Variant[string] map) {
    Variant result = map;

    return result;
}

class ConfigTests : BaseTest {
    mixin UnitTest;

    @Test
    public void identifiers() {
        alias Case = Tuple!(string, "source", bool, "result");
        auto cases = [
            Case("foo", true),
            Case("\u0935\u092e\u0938", true),
            Case("\u73b0\u4ee3\u6c49\u8bed\u5e38\u7528\u5b57\u8868", true),
            Case("foo ", false),
            Case("foo[", false),
            Case("foo [", false),
            Case("foo.", false),
            Case("foo .", false),
            Case("\u0935\u092e\u0938.", false),
            Case("\u73b0\u4ee3\u6c49\u8bed\u5e38\u7528\u5b57\u8868.", false),
            Case("9", false),
            Case("9foo", false),
            Case("hyphenated-key", false)
        ];

        foreach (c; cases) {
            auto r = isIdentifier(c.source);

            assertEquals(c.result, r);
        }
    }

    @Test
    public void badPaths() {
        alias Case = Tuple!(string, "source", string, "message");
        auto cases = [
            Case("foo[1, 2]", "invalid index at (1, 5): expected 1 expression, found 2"),
            Case("foo[1] bar", "Invalid path: foo[1] bar"),
            Case("foo.123", "Invalid path: foo.123"),
            Case("foo.", "expected Word but got EOF"),
            Case("foo[]", "invalid index at (1, 5): expected 1 expression, found 0"),
            Case("foo[1a]", "invalid character in number: 1a"),
            Case("4", null)
        ];

        foreach (c; cases) {
            auto message = format!"Invalid path: %s"(c.source);
            auto e = expectThrows(parsePath(c.source));

            assertIn(message, e.msg);
            if (e.next !is null) {
                assertIn(c.message, e.next.msg);
            }
        }
    }

    @Test
    public void pathIteration() {
        auto node = parsePath("foo[bar].baz['booz'].bozz[3].fizz[::3].fuzz ");
        auto actual = unpackPath(node);
        PathElement[] expected = [
            PathElement(TokenKind.Dot, W("foo")),
            PathElement(TokenKind.LeftBracket, W("bar")),
            PathElement(TokenKind.Dot, W("baz")),
            PathElement(TokenKind.LeftBracket, S("'booz'", "booz")),
            PathElement(TokenKind.Dot, W("bozz")),
            PathElement(TokenKind.LeftBracket, N(3)),
            PathElement(TokenKind.Dot, W("fizz")),
            PathElement(TokenKind.Colon, SN(null, null, N(3))),
            PathElement(TokenKind.Dot, W("fuzz"))
        ];
        assertEquals(expected.length, actual.length);
        for (int i = 0; i < expected.length; i++) {
            assertEquals(expected[i].kind, actual[i].kind);
            compareObjects(expected[i].operand, actual[i].operand);
        }
    }

    @Test
    public void basic() {
        auto cfg = new Config();

        assertTrue(cfg.noDuplicates);
        assertTrue(cfg.strictConversions);
        assertFalse(cfg.cached);
        cfg.cached = true;
        assertTrue(cfg.cached);
    }

    @Test
    public void duplicates() {
        auto path = dataFilePath("derived", "dupes.cfg");
        auto cfg = new Config();

        auto e = expectThrows!ConfigException(cfg.loadFile(path));
        assertEquals(e.message, "Duplicate key foo seen at (4, 1) (previously (1, 1))");
        cfg.noDuplicates = false;
        cfg.loadFile(path);
        assertEquals("not again!", cfg["foo"].get!(string));
    }

    @Test
    public void mainConfig() {
        auto path = dataFilePath("derived", "main.cfg");
        auto cfg = new Config();

        cfg.includePath ~= dataFilePath("base");
        cfg.loadFile(path);
        auto logConf = cfg["logging"].get!(Config);
        assertNotNull(logConf);
        auto keys = ["loggers", "handlers", "formatters", "root"];
        foreach (k; keys) {
            assertTrue(k in logConf);
        }
        Variant v = "bar";
        assertEquals(v, logConf.get("foo", v));
        v = "baz";
        assertEquals(v, logConf.get("foo.bar", v));
        v = "bozz";
        assertEquals(v, logConf.get("handlers.debug.levl", v));
        auto e = expectThrows(logConf.get("handlers.file/filename"));
        assertIn("Invalid path: ", e.msg);
        e = expectThrows(logConf.get("\"handlers.file/filename"));
        assertIn("Invalid path: ", e.msg);
        assertEquals("run/server.log", logConf["handlers.file.filename"].get!(string));
        assertEquals("run/server-debug.log", logConf["handlers.debug.filename"].get!(string));
        assertEquals(["file", "error", "debug"], logConf["root.handlers"].get!(Variant[]));
        assertEquals(["file", "error"], logConf["root.handlers[:2]"].get!(Variant[]));
        assertEquals(["file", "debug"], logConf["root.handlers[::2]"].get!(Variant[]));
        auto test = cfg["test"].get!(Config);
        assertEquals(1.0e-7, test["float"].get!(double));
        assertEquals(0.3, test["float2"].get!(double));
        assertEquals(3.0, test["float3"].get!(double));
        assertEquals(2, test["list[1]"].get!(long));
        assertEquals("b", test["dict.a"].get!(string));
        assertEquals(Date(2019, 3, 28), test["date"].get!(Date));
        auto dt = DateTime(2019, 3, 28, 23, 27, 4);
        auto dur = nsecs(314159000);
        auto tz = new SimpleTimeZone(minutes(330));
        auto expected = SysTime(dt, dur, cast(immutable(TimeZone)) tz);
        assertEquals(expected, test["date_time"].get!(SysTime));
        tz = new SimpleTimeZone(minutes(-330));
        expected = SysTime(dt, dur, cast(immutable(TimeZone)) tz);
        assertEquals(expected, test["neg_offset_time"].get!(SysTime));
        dt = DateTime(2019, 3, 28, 23, 27, 4);
        dur = nsecs(271828000);
        auto st = SysTime(dt, dur);
        assertEquals(st, test["alt_date_time"].get!(SysTime));
        assertEquals(3.3, test["computed"].get!(double));
        assertEquals(2.7, test["computed2"].get!(double));
        assertEquals(0.9, test["computed3"].get!(double));
        assertEquals(10.0, test["computed4"].get!(double));
        assertEquals([
            VS("derived_foo"), VS("derived_bar"), VS("derived_baz"),
            VS("test_foo"), VS("test_bar"), VS("test_baz"),
            VS("base_foo"), VS("base_bar"), VS("base_baz")
        ], cfg["combined_list"]);
        assertEquals([
            "foo_key": VS("base_foo"),
            "bar_key": VS("base_bar"),
            "baz_key": VS("base_baz"),
            "base_foo_key": VS("base_foo"),
            "base_bar_key": VS("base_bar"),
            "base_baz_key": VS("base_baz"),
            "derived_foo_key": VS("derived_foo"),
            "derived_bar_key": VS("derived_bar"),
            "derived_baz_key": VS("derived_baz"),
            "test_foo_key": VS("test_foo"),
            "test_bar_key": VS("test_bar"),
            "test_baz_key": VS("test_baz")
        ], cfg["combined_map_1"]);
        assertEquals([
        "derived_foo_key": VS("derived_foo"),
        "derived_bar_key": VS("derived_bar"),
        "derived_baz_key": VS("derived_baz")
        ], cfg["combined_map_2"]);
        auto n1 = cfg["number_1"].get!(long);
        auto n2 = cfg["number_2"].get!(long);
        assertEquals(n1 & n2, cfg["number_3"].get!(long));
        assertEquals(n1 ^ n2, cfg["number_4"].get!(long));

        alias Case = Tuple!(string, "source", string, "message");

        auto cases = [
            Case("logging[4]", "string required, but found 4"),
            Case("logging[:4]", "slices can only operate on lists"),
            Case("no_such_key", "Not found in configuration: no_such_key")
        ];

        foreach (c; cases) {
            try {
                cfg[c.source];
            }
            catch (ConfigException ce) {
                assertIn(ce.msg, c.message);
            }
        }
    }

    @Test
    public void exampleConfig() {
        auto path = dataFilePath("derived", "example.cfg");
        auto cfg = new Config();

        cfg.includePath ~= dataFilePath("base");
        cfg.loadFile(path);

        // strings

        assertEquals(cfg["snowman_escaped"], cfg["snowman_unescaped"]);
        assertEquals("\u2603", cfg["snowman_escaped"]);
        assertEquals("\U0001f602",cfg[ "face_with_tears_of_joy"]);
        assertEquals("\U0001f602", cfg["unescaped_face_with_tears_of_joy"]);
        auto strings = cfg["strings"].get!(Variant[]);
        assertEquals("Oscar Fingal O'Flahertie Wills Wilde", strings[0]);
        assertEquals("size: 5\"", strings[1]);
        version(Windows) {
            assertEquals("Triple quoted form\r\ncan span\r\n'multiple' lines", strings[2]);
            assertEquals("with \"either\"\r\nkind of 'quote' embedded within", strings[3]);
        }
        else {
            assertEquals("Triple quoted form\ncan span\n'multiple' lines", strings[2]);
            assertEquals("with \"either\"\nkind of 'quote' embedded within", strings[3]);
        }

        // special strings

        static import std.process;

        assertEquals(std.process.environment.get("HOME"), cfg["special_value_2"]);
        auto sv3 = cfg["special_value_3"].get!(SysTime);
        assertEquals(2019, sv3.year);
        assertEquals(3, sv3.month);
        assertEquals(28, sv3.day);
        assertEquals(23, sv3.hour);
        assertEquals(27, sv3.minute);
        assertEquals(4, sv3.second);
        assertEquals(nsecs(314159000), sv3.fracSecs);
        assertEquals(minutes(330), (cast(SimpleTimeZone) sv3.timezone).utcOffset);
        assertEquals("bar", cfg["special_value_4"]);

        // integers

        assertEquals(123L, cfg["decimal_integer"]);
        assertEquals(0x123L, cfg["hexadecimal_integer"]);
        assertEquals(83L, cfg["octal_integer"]);
        assertEquals(0b000100100011L, cfg["binary_integer"]);

        // floats

        assertEquals(123.456, cfg["common_or_garden"].get!(double));
        assertEquals(0.123, cfg["leading_zero_not_needed"].get!(double));
        assertEquals(123.0, cfg["trailing_zero_not_needed"].get!(double));
        assertEquals(1.0e6, cfg["scientific_large"].get!(double));
        assertEquals(1.0e-7, cfg["scientific_small"].get!(double));
        assertEquals(3.14159, cfg["expression_1"].get!(double));

        // complex

        assertEquals(complex(3.0, 2.0), cfg["expression_2"]);
        assertEquals(complex(1.0, 3.0), cfg["list_value[4]"]);

        // boolean

        assertEquals(true, cfg["boolean_value"]);
        assertEquals(false, cfg["opposite_boolean_value"]);
        assertEquals(false, cfg["computed_boolean_2"]);
        assertEquals(true, cfg["computed_boolean_1"]);

        // list

        assertEquals([VS("a"), VS("b"), VS("c")], cfg["incl_list"]);

        // mapping

        assertEquals(["bar": VS("baz"), "foo": VS("bar")], cfg["incl_mapping"].asDict());
        assertEquals(["baz": VS("bozz"), "fizz": VS("buzz")], cfg["incl_mapping_body"].asDict());
    }

    @Test
    public void context() {
        auto context = ["bozz": VS("bozz-bozz")];
        auto path = dataFilePath("derived", "context.cfg");
        auto cfg = new Config();
        cfg.context = context;
        cfg.loadFile(path);
        assertEquals("bozz-bozz", cfg["baz"]);
        try {
            cfg["bad"];
        }
        catch (ConfigException ce) {
            assertIn(ce.msg, "unknown variable 'not_there'");
        }
    }

    @Test
    public void expressions() {
        auto path = dataFilePath("derived", "test.cfg");
        auto cfg = new Config(path);

        assertEquals(["a": VS("b"), "c": VS("d")], cfg["dicts_added"]);
        // nested lists and maps need to be dressed up as Variants.
        Variant v1 = ["b": VS("c"), "w": VS("x")];
        Variant v2 = ["e": VS("f"), "y": VS("z")];
        assertEquals(["a": v1, "d": v2], cfg["nested_dicts_added"]);
        assertEquals([VS("a"), VN(1), VS("b"), VN(2)], cfg["lists_added"]);
        assertEquals([VN(1), VN(2)], cfg["list[:2]"]);
        assertEquals(["a": VS("b")], cfg["dicts_subtracted"]);
        Variant[string] empty;
        assertEquals(empty, cfg["nested_dicts_subtracted"]);
        assertEquals([
            "a_list": VL([VN(1), VN(2), VM(["a": VN(3)])]),
            "a_map": VM(["k1": VL([VS("b"), VS("c"), VM(["d": VS("e")])])])
        ], cfg["dict_with_nested_stuff"]);
        assertEquals([VN(1), VN(2)], cfg["dict_with_nested_stuff.a_list[:2]"]);
        assertEquals(-4L, cfg["unary"]);
        assertEquals("mno", cfg["abcdefghijkl"]);
        assertEquals(8L, cfg["power"]);
        assertEquals(2.5, cfg["computed5"].get!(double));
        assertEquals(2L, cfg["computed6"]);
        assertEquals(complex(3.0, 1.0), cfg["c3"]);
        assertEquals(complex(5.0, 5.0), cfg["c4"]);
        assertEquals(2L, cfg["computed8"]);
        assertEquals(160L, cfg["computed9"]);
        assertEquals(62L, cfg["computed10"]);
        assertEquals("A-4 a test_foo true 10 1e-07 1 b [a, c, e, g]Z", cfg["interp"]);
        assertEquals("{a: b}", cfg["interp2"]);

        alias Case = Tuple!(string, "source", string, "message");

        auto cases = [
            Case("bad_include", "@ operand must be a string"),
            Case("computed7", "not found in configuration: float4"),
            Case("bad_interp", "unable to convert ")
        ];

        foreach (c; cases) {
            try {
                cfg[c.source];
            }
            catch (ConfigException ce) {
                assertIn(c.message, ce.msg);
            }
        }
    }

    @Test
    public void forms() {
        auto path = dataFilePath("derived", "forms.cfg");
        auto cfg = new Config();

        cfg.includePath ~= dataFilePath("base");
        cfg.loadFile(path);

        alias Case = Tuple!(string, "source", Variant, "value");

        auto cases = [
            Case("modals.deletion.contents[0].id", VS("frm-deletion")),
            Case("refs.delivery_address_field", VM([
                "kind": VS("field"),
                "type": VS("textarea"),
                "name": VS("postal_address"),
                "label": VS("Postal address"),
                "label_i18n": VS("postal-address"),
                "short_name": VS("address"),
                "placeholder": VS("We need this for delivering to you"),
                "ph_i18n": VS("your-postal-address"),
                "message": VS(" "),
                "required": VB(true),
                "attrs": VM(["minlength": VN(10)]),
                "grpclass": VS("col-md-6")
            ])),
            Case("refs.delivery_instructions_field", VM([
                "kind": VS("field"),
                "type": VS("textarea"),
                "name": VS("delivery_instructions"),
                "label": VS("Delivery Instructions"),
                "short_name": VS("notes"),
                "placeholder": VS("Any special delivery instructions?"),
                "message": VS(" "),
                "label_i18n": VS("delivery-instructions"),
                "ph_i18n": VS("any-special-delivery-instructions"),
                "grpclass": VS("col-md-6")
            ])),
            Case("refs.verify_field", VM([
                "kind": VS("field"),
                "type": VS("input"),
                "name": VS("verification_code"),
                "label": VS("Verification code"),
                "label_i18n": VS("verification-code"),
                "short_name": VS("verification code"),
                "placeholder": VS("Your verification code (NOT a backup code)"),
                "ph_i18n": VS("verification-not-backup-code"),
                "attrs": VM([
                        "minlength": VN(6),
                        "maxlength": VN(6),
                        "autofocus": VB(true)]),
                "append": VM([
                        "label": VS("Verify"),
                        "type": VS("submit"),
                        "classes": VS("btn-primary")]),
                "message": VS(" "),
                "required": VB(true)
            ])),
            Case("refs.signup_password_field", VM([
                "kind": VS("field"),
                "type": VS("password"),
                "label": VS("Password"),
                "label_i18n": VS("password"),
                "message": VS(" "),
                "name": VS("password"),
                "ph_i18n": VS("password-wanted-on-site"),
                "placeholder": VS("The password you want to use on this site"),
                "required": VB(true),
                "toggle": VB(true)
            ])),
            Case("refs.signup_password_conf_field", VM([
                "kind": VS("field"),
                "type": VS("password"),
                "name": VS("password_conf"),
                "label": VS("Password confirmation"),
                "label_i18n": VS("password-confirmation"),
                "placeholder": VS("The same password, again, to guard against mistyping"),
                "ph_i18n": VS("same-password-again"),
                "message": VS(" "),
                "toggle": VB(true),
                "required": VB(true)
            ])),
            Case("fieldsets.signup_ident[0].contents[0]", VM([
                "kind": VS("field"),
                "type": VS("input"),
                "name": VS("display_name"),
                "label": VS("Your name"),
                "label_i18n": VS("your-name"),
                "placeholder": VS("Your full name"),
                "ph_i18n": VS("your-full-name"),
                "message": VS(" "),
                "data_source": VS("user.display_name"),
                "required": VB(true),
                "attrs": VM(["autofocus": VB(true)]),
                "grpclass": VS("col-md-6")
            ])),
            Case("fieldsets.signup_ident[0].contents[1]", VM([
                "kind": VS("field"),
                "type": VS("input"),
                "name": VS("familiar_name"),
                "label": VS("Familiar name"),
                "label_i18n": VS("familiar-name"),
                "placeholder": VS("If not just the first word in your full name"),
                "ph_i18n": VS("if-not-first-word"),
                "data_source": VS("user.familiar_name"),
                "message": VS(" "),
                "grpclass": VS("col-md-6")
            ])),
            Case("fieldsets.signup_ident[1].contents[0]", VM([
                "kind": VS("field"),
                "type": VS("email"),
                "name": VS("email"),
                "label": VS("Email address (used to sign in)"),
                "label_i18n": VS("email-address"),
                "short_name": VS("email address"),
                "placeholder": VS("Your email address"),
                "ph_i18n": VS("your-email-address"),
                "message": VS(" "),
                "required": VB(true),
                "data_source": VS("user.email"),
                "grpclass": VS("col-md-6")
            ])),
            Case("fieldsets.signup_ident[1].contents[1]", VM([
                "kind": VS("field"),
                "type": VS("input"),
                "name": VS("mobile_phone"),
                "label": VS("Phone number"),
                "label_i18n": VS("phone-number"),
                "short_name": VS("phone number"),
                "placeholder": VS("Your phone number"),
                "ph_i18n": VS("your-phone-number"),
                "classes": VS("numeric"),
                "message": VS(" "),
                "prepend": VM(["icon": VS("phone")]),
                "attrs": VM(["maxlength": VN(10)]),
                "required": VB(true),
                "data_source": VS("customer.mobile_phone"),
                "grpclass": VS("col-md-6")
            ]))
        ];

        foreach (c; cases) {
            assertEquals(c.value, cfg[c.source]);
        }
    }

    @Test
    public void pathAcrossIncludes() {
        auto path = dataFilePath("base", "main.cfg");
        auto cfg = new Config(path);

        assertEquals("run/server.log", cfg["logging.appenders.file.filename"]);
        assertTrue(cfg["logging.appenders.file.append"].get!(bool));
        assertEquals("run/server-errors.log", cfg["logging.appenders.error.filename"]);
        assertFalse(cfg["logging.appenders.error.append"].get!(bool));
        assertEquals("https://freeotp.github.io/", cfg["redirects.freeotp.url"]);
        assertFalse(cfg["redirects.freeotp.permanent"].get!(bool));
    }

    @Test
    public void badConversions() {
        auto cases = ["foo"];
        auto cfg = new Config();

        foreach (c; cases) {
            cfg.strictConversions = true;
            try {
                cfg.convertString(c);
            }
            catch (ConfigException ce) {
                assertIn(ce.msg, format!"unable to convert '%s'"(c));
            }
            cfg.strictConversions = false;
            auto s = cfg.convertString(c);
            assertEquals(c, s);
        }
    }

    @Test
    public void sources() {
        auto cases = [
            "foo[::2]",
            "foo[:]",
            "foo[:2]",
            "foo[2:]",
            "foo[::1]",
            "foo[::-1]"
        ];

        foreach (c; cases) {
            auto node = parsePath(c);
            auto s = toSource(node);
            assertEquals(c, s);
        }
    }

    @Test
    public void circularReferences() {
        auto path = dataFilePath("derived", "test.cfg");
        auto cfg = new Config(path);

        alias Case = Tuple!(string, "source", string, "message");

        auto cases = [
            Case("circ_list[1]", "Circular reference: circ_list[1] (42, 7)"),
            Case("circ_map.a", "Circular reference: circ_map.a (49, 10), circ_map.b (47, 10), circ_map.c (48, 10)"),
        ];

        foreach (c; cases) {
            try {
                cfg[c.source];
            }
            catch (CircularReferenceException cre) {
                assertIn(cre.msg, c.message);
            }
        }
    }

    @Test
    public void slicesAndIndices() {
        auto path = dataFilePath("derived", "test.cfg");
        auto cfg = new Config(path);
        auto theList = [VS("a"), VS("b"), VS("c"), VS("d"), VS("e"), VS("f"), VS("g")];

        // slices

        assertEquals(theList, cfg["test_list[:]"]);
        assertEquals(theList, cfg["test_list[::]"]);
        assertEquals(theList, cfg["test_list[:20]"]);
        assertEquals(theList, cfg["test_list[-20:20]"]);
        assertEquals([VS("a"), VS("b"), VS("c"), VS("d")], cfg["test_list[-20:4]"]);
        assertEquals([VS("c"), VS("d"), VS("e"), VS("f"), VS("g")], cfg["test_list[2:]"]);
        assertEquals([VS("e"), VS("f"), VS("g")], cfg["test_list[-3:]"]);
        assertEquals([VS("f"), VS("e"), VS("d")], cfg["test_list[-2:2:-1]"]);
        assertEquals([VS("g"), VS("f"), VS("e"), VS("d"), VS("c"), VS("b"), VS("a")], cfg["test_list[::-1]"]);
        assertEquals([VS("c"), VS("e")], cfg["test_list[2:-2:2]"]);
        assertEquals([VS("a"), VS("c"), VS("e"), VS("g")], cfg["test_list[::2]"]);
        assertEquals([VS("a"), VS("d"), VS("g")], cfg["test_list[::3]"]);
        assertEquals([VS("a"), VS("g")], cfg["test_list[::2][::3]"]);

        // indices

        foreach (i, v; theList.enumerate()) {
            assertEquals(v, cfg[format!"test_list[%d]"(i)]);
        }

        // negative indices

        int n = to!int(theList.length);
        for (int i = n; i > 0; i--) {
            assertEquals(theList[n - i], cfg[format!"test_list[-%d]"(i)]);
        }

        // invalid indices

        auto invalid = [n, n + 1, -(n + 1), -(n + 2)];

        foreach(i; invalid) {
            try {
                cfg[format!"test_list[%d]"(i)];
            }
            catch (BadIndexException bie) {

            }
        }
    }

    @Test
    public void absoluteIncludePath() {
        auto path = absolutePath(dataFilePath("derived", "test.cfg"));
        auto s = "test: @'foo'".replace("foo", path.replace("\\", "/"));
        auto r = inputRangeObject(s.representation.map!(b => ubyte(b)));
        auto cfg = new Config(r);

        assertEquals(2, cfg["test.computed6"].get!(long));
    }

    @Test
    public void nestedIncludePath() {
        auto path = dataFilePath("base", "top.cfg");
        auto cfg = new Config(path);

        cfg.includePath ~= dataFilePath("derived");
        cfg.includePath ~= dataFilePath("another");
        assertEquals(42, cfg["level1.level2.final"].get!(long));
    }
}
