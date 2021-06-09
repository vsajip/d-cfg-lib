/*
 * Copyright (c) 2018-2021, Red Dove Consultants Limited.
 *
 * See LICENSE file for license terms.
 */
module config;

import core.time;
import std.algorithm;
import std.array;
import std.ascii;
import std.complex;
import std.conv;
import std.datetime;
import std.datetime.systime;
import std.datetime.timezone;
import std.file;
import std.format;
import std.math;
import std.path;
import std.process;
import std.range;
import std.regex;
import std.stdio;
import std.string;
import std.traits;
import std.typecons;
import std.uni;
import std.variant;

class Location {
    int line;
    int column;

    this(int line = 1, int column = 1) {
        this.line = line;
        this.column = column;
    }

    this(ref Location other) {
        line = other.line;
        column = other.column;
    }

    void update(ref Location other) {
        line = other.line;
        column = other.column;
    }

    void nextLine() {
        line++;
        column = 1;
    }

    override string toString() {
        return format!"(%s, %s)"(line, column);
    }
}

class RecognizerException : Exception {
    this(string msg, string file = __FILE__, size_t line = __LINE__) {
        super(msg, file, line);
    }
}

class DecodingException : RecognizerException {
    immutable(ubyte)[] invalid;

    this(string msg, string file = __FILE__, size_t line = __LINE__) {
        super(msg, file, line);
    }
}

class TokenizerException : RecognizerException {
    Location location;

    this(string msg, string file = __FILE__, size_t line = __LINE__) {
        super(msg, file, line);
    }
}

class ParserException : TokenizerException {
    this(string msg, string file = __FILE__, size_t line = __LINE__) {
        super(msg, file, line);
    }
}

enum TokenKind {
    EOF = 0,
    Word,
    Integer,
    Float,
    String,
    Newline,
    LeftCurly,
    RightCurly,
    LeftBracket,
    RightBracket,
    LeftParenthesis,
    RightParenthesis,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    Assign,
    Equal,
    Unequal,
    AltUnequal,
    LeftShift,
    RightShift,
    Dot,
    Comma,
    Colon,
    At,
    Plus,
    Minus,
    Star,
    Power,
    Slash,
    SlashSlash,
    Modulo,
    BackTick,
    Dollar,
    True,
    False,
    None,
    Is,
    In,
    Not,
    And,
    Or,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    BitwiseComplement,
    Complex,
    IsNot,
    NotIn
}

abstract class ASTNode {
    TokenKind kind;
}

class Token : ASTNode {
    string    text;
    Variant   value;
    Location  start;
    Location  end;

    this(TokenKind kind, string text, Variant value) {
        this.kind = kind;
        this.text = text;
        this.value = value;
        start = new Location();
        end = new Location();
    }

    this(ref Token other) {
        kind = other.kind;
        text = other.text;
        value = other.value;
        start = new Location(other.start);
        end = new Location(other.end);
    }

    override string toString() {
        return format!"Token(%s:%s:%s)"(kind, text, value);
    }
}

class Decoder {
    InputRange!(ubyte) r;

    this(InputRange!(ubyte) r) {
        this.r = r;
    }

    public bool atEnd() {
        return r.empty();
    }

    // See http://bjoern.hoehrmann.de/utf-8/decoder/dfa/

    const int UTF8_ACCEPT = 0;
    const int UTF8_REJECT = 12;

    static ubyte[] UTF8_LOOKUP = [
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,  9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,
    7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,  7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,
    8,8,2,2,2,2,2,2,2,2,2,2,2,2,2,2,  2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
    10,3,3,3,3,3,3,3,3,3,3,3,3,4,3,3, 11,6,6,6,5,8,8,8,8,8,8,8,8,8,8,8,

    // The second part is a transition table that maps a combination
    // of a state of the automaton and a character class to a state.
    0,12,24,36,60,96,84,12,12,12,48,72, 12,12,12,12,12,12,12,12,12,12,12,12,
    12, 0,12,12,12,12,12, 0,12, 0,12,12, 12,24,12,12,12,12,12,24,12,24,12,12,
    12,12,12,12,12,12,12,24,12,12,12,12, 12,24,12,12,12,12,12,12,12,24,12,12,
    12,12,12,12,12,12,12,36,12,36,12,12, 12,36,12,12,12,12,12,36,12,36,12,12,
    12,36,12,12,12,12,12,12,12,12,12,12,
    ];

    dchar decode() {
        int state = UTF8_ACCEPT;
        auto code_point = 0;
        ubyte[] bytes = new ubyte[0];

        while (!r.empty()) {
            ubyte b = r.front;

            bytes.length++;
            bytes[bytes.length - 1] = b;
            auto kind = UTF8_LOOKUP[b];

            r.popFront();
            if (state != UTF8_ACCEPT) {
                code_point = (b & 0x3F) | (code_point << 6);
            }
            else {
                code_point = (0xFF >> kind) & b;
            }
            state = UTF8_LOOKUP[256 + state + kind];
            if ((state == UTF8_ACCEPT) || (state == UTF8_REJECT)) {
                break ;
            }
        }
        if (state == UTF8_ACCEPT) {
            return cast(dchar) code_point;
        }
        auto e = new DecodingException("Decoding error");
        e.invalid = bytes.idup;
        throw e;
    }
}

class PushBackInfo {
    dchar c;
    Location pos;

    this(dchar c, Location pos) {
        this.c = c;
        this.pos = new Location(pos);
    }
}

final class Stack(T)
{
    private T[] data;

    @property size_t capacity()
    {
        return data.length;
    }

    private size_t _length = 0;

    @property size_t length()
    {
        return _length;
    }

    this(size_t initialCapacity=5)
    {
        data.length = initialCapacity;
    }

    private this(Stack!T s)
    {
        data = s.data.dup;
        _length = s._length;
    }

    /*
    ref T opIndex(size_t i)
    {
        debug if(i >= _length)
            throw new Exception("Invalid index");

        return data[i];
    }

    T[] opSlice(size_t a, size_t b)
    {
        debug if(a >= _length || b > _length)
            throw new Exception("Invalid index");

        return data[a..b];
    }
    */

    private void expand()
    {
        // add 1 initially, then double
        size_t numMore = data.length;
        if (numMore == 0)
            numMore = 1;
        data.length += numMore;
    }

    /*
    void compact()
    {
        data.length = _length;
    }

    void clear()
    {
        _length = 0;
        data.clear();
    }
    */

    void opOpAssign(string op)(T item) if (op=="~")
    {
        if (_length == data.length)
            expand();

        data[_length] = item;
        _length++;
    }

    /*
    void opOpAssign(string op)(T[] items) if(op=="~")
    {
        while(_length + items.length >= data.length)
            expand();

        data[ _length .. _length + items.length ] = items;
        _length += items.length;
    }
    */

    /*
    void pop(size_t num=1)
    {
        debug if(num > _length)
            throw new Exception("Invalid index");

        _length -= num;
    }
    */

    T pop() {
        _length--;
        return data[_length];
    }

    /*
    @property Stack!T dup()
    {
        return new Stack!T(this);
    }

    int opApply(int delegate(ref T) dg)
    {
        int result = 0;
        foreach (ref T item; data[0.._length])
        {
            result = dg(item);
            if(result)
                break;
        }
        return result;
    }

    int opApply(int delegate(ref size_t, ref T) dg)
    {
        int result = 0;
        foreach (size_t i, ref T item; data[0.._length])
        {
            result = dg(i, item);
            if(result)
                break;
        }
        return result;
    }
    */
}

immutable static Object NullValue = new Object();

class Tokenizer {
    Decoder decoder;
    Stack!PushBackInfo pushedBack;
    Location charLocation;
    Location location;

    immutable static TokenKind[dchar] punctuation;
    immutable static TokenKind[string] keywords;
    immutable static Variant[TokenKind] keywordValues;
    immutable static dchar[dchar] escapes;

    shared static this() {
        punctuation = [
            ':': TokenKind.Colon,
            '-': TokenKind.Minus,
            '+': TokenKind.Plus,
            '*': TokenKind.Star,
            '/': TokenKind.Slash,
            '%': TokenKind.Modulo,
            ',': TokenKind.Comma,
            '{': TokenKind.LeftCurly,
            '}': TokenKind.RightCurly,
            '[': TokenKind.LeftBracket,
            ']': TokenKind.RightBracket,
            '(': TokenKind.LeftParenthesis,
            ')': TokenKind.RightParenthesis,
            '@': TokenKind.At,
            '$': TokenKind.Dollar,
            '<': TokenKind.LessThan,
            '>': TokenKind.GreaterThan,
            '!': TokenKind.Not,
            '~': TokenKind.BitwiseComplement,
            '&': TokenKind.BitwiseAnd,
            '|': TokenKind.BitwiseOr,
            '^': TokenKind.BitwiseXor,
            '.': TokenKind.Dot
        ];

        keywords = [
            "true": TokenKind.True,
            "false": TokenKind.False,
            "null": TokenKind.None,
            "is": TokenKind.Is,
            "in": TokenKind.In,
            "not": TokenKind.Not,
            "and": TokenKind.And,
            "or": TokenKind.Or
        ];

        Variant tv = true;
        Variant fv = false;
        Variant nv = NullValue;

        keywordValues = [
            TokenKind.True: tv,
            TokenKind.False: fv,
            TokenKind.None: nv
        ];

        escapes = [
            'a': '\u0007',
            'b': '\b',
            'f': '\u000C',
            'n': '\n',
            'r': '\r',
            't': '\t',
            'v': '\u000B',
            '\\': '\\',
            '\'': '\'',
            '"': '"'
        ];
    }


    this(InputRange!(ubyte) r) {
        decoder = new Decoder(r);
        pushedBack = new Stack!PushBackInfo();
        charLocation = new Location();
        location = new Location();
    }

    public bool atEnd() {
        return decoder.atEnd();
    }

    public dchar getChar() {
        dchar result = '\0';

        if (pushedBack.length > 0) {
            auto pb = pushedBack.pop();

            result = pb.c;
            charLocation.update(pb.pos);
            location.update(pb.pos);
        }
        else {
            charLocation.update(location);
            if (!atEnd()) {
                result = decoder.decode();
            }
        }
        if (result != '\0') {
            if (result == '\n') {
                location.nextLine();
            }
            else {
                location.column++;
            }
        }
        return result;
    }

    public void pushBack(dchar c) {
        if (c != '\0') {
            pushedBack ~= new PushBackInfo(c, charLocation);
        }
    }

    string parseEscapes(dchar[] text) {
        string result;
        auto i = text.countUntil('\\');

        if (i < 0) {
            result = to!string(text);
        }
        else {
            dchar[] chars = new dchar[0];
            auto failed = false;

            while (i >= 0) {
                auto n = text.length;

                if (i > 0) {
                    chars ~= text[0 .. i];
                }
                auto c = text[i + 1];
                if (c in escapes) {
                    chars ~= escapes[c];
                    i += 2;
                }
                else if ((c == 'x') || (c == 'X') || (c == 'u') || (c == 'U')) {
                    int slen = ((c == 'x') || (c == 'X')) ? 4 : ((c == 'u') ? 6 : 10);

                    if ((i + slen) > n) {
                        failed = true;
                        break;
                    }
                    auto p = text[i + 2 .. i + slen];

                    try {
                        auto j = to!uint(p, 16);

                        if (((j >= 0xd800) && (j <= 0xdfff)) || (j >= 0x110000)) {
                            failed = true;
                            break;
                        }
                        chars ~= to!dchar(j);
                        i += slen;
                    }
                    catch (ConvException) {
                        failed = true;
                        break;
                    }
                }
                else {
                    failed = true;
                    break;
                }
                text = text[i .. $];
                i = text.countUntil('\\');
            }
            if (failed) {
                throw new TokenizerException(format!"invalid escape sequence at index %d"(i));
            }
            chars ~= text;
            result = to!string(chars);
        }
        return result;
     }

    TokenKind getNumber(ref dchar[] text, ref Variant value, ref Location startLocation, ref Location endLocation) {
        TokenKind result = TokenKind.Integer;
        auto inExponent = false;
        auto radix = 0;
        auto dotSeen = text.countUntil('.') >= 0;
        auto lastWasDigit = text[$ - 1].isDigit();
        dchar c;

        void appendChar(dchar c) {
            text ~= c;
            endLocation.update(charLocation);
        }

        while (true) {
            c = getChar();

            if (c == '\0') {
                break;
            }
            if (c == '.') {
                dotSeen = true;
            }
            if (c == '_') {
                if (lastWasDigit) {
                    appendChar(c);
                    lastWasDigit = false;
                    continue;
                }
                auto msg = format!"invalid '_' in number: %s%c"(text, c);
                auto e = new TokenizerException(msg);

                e.location = charLocation;
                throw e;
            }
            lastWasDigit = false; // unless set in one of the clauses below
            if ((radix == 0) && (c >= '0') && (c <= '9')) {
                appendChar(c);
                lastWasDigit = true;
            }
            else if ((radix == 2) && (c >= '0') && (c <= '1')) {
                appendChar(c);
                lastWasDigit = true;
            }
            else if ((radix == 8) && (c >= '0') && (c <= '7')) {
                appendChar(c);
                lastWasDigit = true;
            }
            else if ((radix == 16) && isHexDigit(c)) {
                appendChar(c);
                lastWasDigit = true;
            }
            else if (((c == 'o') || (c == 'O') || (c == 'x') || (c == 'X') ||
                      (c == 'b') || (c == 'B')) && (text.length == 1) && (text[0] == '0')) {
                radix = ((c == 'o') || (c == 'O')) ? 8 : (((c == 'x') || (c == 'X')) ? 16 : 2);
                appendChar(c);
            }
            else if ((radix == 0) && (c == '.') && !inExponent && (text.countUntil(c) < 0)) {
                appendChar(c);
            }
            else if ((radix == 0) && (c == '-') && (text[1 .. $].countUntil('-') < 0) && inExponent) {
                appendChar(c);
            }
            else if ((radix == 0) && ((c == 'e') || (c == 'E')) && (text.countUntil('e') < 0) &&
                     (text.countUntil('E') < 0) && (text[$ - 1] != '_')) {
                appendChar(c);
                inExponent = true;
            }
            else {
                break;
            }
        }
        // Reached the end of the actual number part. Before checking for complex,
        // ensre that the lasy char wasn't an underscore.
        if (text[$ - 1] == '_') {
            auto msg = format!"invalid '_' at end of number: %s"(text);
            auto e = new TokenizerException(msg);

            e.location = charLocation;
            e.location.column--;
            throw e;
        }
        if ((radix == 0) && ((c == 'j') || (c == 'J'))) {
            appendChar(c);
            result = TokenKind.Complex;
        }
        else {
            // not allowed to have a letter or digit which wasn't accepted
            if ((c != '.') && !std.uni.isAlphaNum(c)) {
                pushBack(c);
            }
            else {
                auto msg = format!"invalid character in number: %s%c"(text, c);
                auto e = new TokenizerException(msg);

                e.location = charLocation;
                throw e;
            }
        }
        auto s = to!string(text).replace("_", "");

        if (radix != 0) {
            value = to!long(s[2 .. $], radix);
        }
        else if (result == TokenKind.Complex) {
            auto imaginary = to!double(text[0 .. $ - 1]);
            value = complex(0.0, imaginary);
        }
        else if (inExponent || dotSeen) {
            result = TokenKind.Float;
            value = to!double(s);
        }
        else {
            radix = (text[0] == '0') ? 8 : 10;
            try {
                value = to!long(s, radix);
            }
            catch (ConvException) {
                auto e = new TokenizerException(format!"invalid character in number: %s"(text));

                e.location = new Location(startLocation);
                throw e;
            }
        }
        return result;
    }

    public Token getToken() {
        TokenKind kind = TokenKind.EOF;
        dchar[] text = new dchar[0];
        string s = "";
        Variant value = null;
        Location start = new Location();
        Location end = new Location();

        void appendChar(dchar c) {
            text ~= c;
            end.update(charLocation);
        }

        for (;;) {
            auto c = getChar();
            start.update(charLocation);
            end.update(charLocation);
            if (c == '\0') {
                break;
            }
            if ((c != '\n') && (c != '\r') && std.uni.isWhite(c)) {
                continue;
            }
            appendChar(c);
            // we don't use a switch because we often need to
            // dispatch on miscellaneous conditions
            if (c == '#') {
                while (((c = getChar()) != '\0') && (c != '\n')) {
                    appendChar(c);
                }
                kind = TokenKind.Newline;
                break;
            }
            else if (c == '\n') {
                kind = TokenKind.Newline;
                end.update(location);
                end.column--;
                break;
            }
            else if (c == '\r') {
                c = getChar();
                if (c != '\n') {
                    pushBack(c);
                }
                kind = TokenKind.Newline;
                location.nextLine();
                break;
            }
            else if (c == '\\') {
                c = getChar();
                if (c != '\n') {
                    auto e = new TokenizerException(format!"unexpected character: \\");

                    e.location = new Location(charLocation);
                    throw e;
                }
                continue;
            }
            else if ((c == '_') || std.uni.isAlpha(c)) {
                kind = TokenKind.Word;
                value = null;
                while (((c = getChar()) != '\0') && ((c == '_') || std.uni.isAlphaNum(c))) {
                    appendChar(c);
                }
                pushBack(c);
                s = to!string(text);
                if (s in keywords) {
                    kind = keywords[s];
                    if (kind in keywordValues) {
                        // cast is to remove immutability
                        value = cast(Variant) keywordValues[kind];
                    }
                }
                break;
            }
            else if (c.isDigit()) {
                kind = getNumber(text, value, start, end);
                break;
            }
            else if (c == '=') {
                c = getChar();

                if (c != '=') {
                    kind = TokenKind.Assign;
                    pushBack(c);
                }
                else {
                    kind = TokenKind.Equal;
                    appendChar(c);
                }
                break;
            }
            else if (c in punctuation) {
                kind = punctuation[c];
                if (c == '.') {
                    c = getChar();
                    if (!c.isDigit()) {
                        pushBack(c);
                    }
                    else {
                        appendChar(c);
                        kind = getNumber(text, value, start, end);
                    }
                }
                else if (c == '-') {
                    c = getChar();
                    if (!c.isDigit() && (c != '.')) {
                        pushBack(c);
                    }
                    else {
                        appendChar(c);
                        kind = getNumber(text, value, start, end);
                    }
                }
                else if (c == '<') {
                    auto append = false;

                    c = getChar();
                    if (c == '=') {
                        kind = TokenKind.LessThanOrEqual;
                        append = true;
                    }
                    else if (c == '>') {
                        kind = TokenKind.AltUnequal;
                        append = true;
                    }
                    else if (c == '<') {
                        kind = TokenKind.LeftShift;
                        append = true;
                    }
                    if (append) {
                        appendChar(c);
                    }
                    else {
                        pushBack(c);
                    }
                }
                else if (c == '>') {
                    auto append = false;

                    c = getChar();
                    if (c == '=') {
                        kind = TokenKind.GreaterThanOrEqual;
                        append = true;
                    }
                    else if (c == '>') {
                        kind = TokenKind.RightShift;
                        append = true;
                    }
                    if (append) {
                        appendChar(c);
                    }
                    else {
                        pushBack(c);
                    }
                }
                else if (c == '!') {
                    c = getChar();
                    if (c == '=') {
                        kind = TokenKind.Unequal;
                        appendChar(c);
                    }
                    else {
                        pushBack(c);
                    }
                }
                else if (c == '/') {
                    c = getChar();
                    if (c != '/') {
                        pushBack(c);
                    }
                    else {
                        kind = TokenKind.SlashSlash;
                        appendChar(c);
                    }
                }
                else if (c == '*') {
                    c = getChar();
                    if (c != '*') {
                        pushBack(c);
                    }
                    else {
                        kind = TokenKind.Power;
                        appendChar(c);
                    }
                }
                else if ((c == '&') || (c == '|')) {
                    auto c2 = getChar();

                    if (c2 != c) {
                        pushBack(c2);
                    }
                    else {
                        if (c2 == '&') {
                            kind = TokenKind.And;
                        }
                        else {
                            kind = TokenKind.Or;
                        }
                        appendChar(c2);
                    }
                }
                break;
            }
            else if (c == '`') {
                kind = TokenKind.BackTick;
                while ((c = getChar()) != '\0') {
                    appendChar(c);
                    if (c == '`') {
                        break;
                    }
                }
                if (c == '\0') {
                    auto e = new TokenizerException(format!"unterminated `-string: %s"(text));

                    e.location = start;
                    throw e;
                }
                s = to!string(text);
                value = parseEscapes(text[1 .. $ - 1]);
                break;
            }
            else if ((c == '\'') || (c == '"')) {
                auto quote = c;
                auto multiLine = false;
                auto escaped = false;
                kind = TokenKind.String;
                // first check for a triple quote
                auto c1 = getChar();
                auto c1Loc = new Location(charLocation);

                if (c1 != quote) {
                    pushBack(c1);
                }
                else {
                    auto c2 = getChar();

                    if (c2 != quote) {
                        pushBack(c2);
                        if (c2 == '\0') {
                            charLocation.update(c1Loc);
                        }
                        pushBack(c1);
                    }
                    else {
                        multiLine = true;
                        appendChar(quote);
                        appendChar(quote);
                    }
                }
                auto qlen = text.length;
                while ((c = getChar()) != '\0') {
                    appendChar(c);
                    if ((c == quote) && !escaped) {
                        if (!multiLine || (text.length) >= 6 && (text[$-3..$] == text[0..3]) && (text[$ - 4] != '\\')) {
                            break;
                        }
                    }
                    if (c == '\\') {
                        escaped = !escaped;
                    }
                    else {
                        escaped = false;
                    }
                }
                if (c == '\0') {
                    auto e = new TokenizerException(format!"unterminated string: %s"(text));

                    e.location = start;
                    throw e;
                }
                s = to!string(text);
                value = parseEscapes(text[qlen .. $ - qlen]);
                break;
            }
            else {
                auto e = new TokenizerException(format!"unexpected character: %c"(c));

                e.location = new Location(charLocation);
                throw e;
            }
        }
        if (s.length == 0) {
            s = to!string(text);
        }
        auto result = new Token(kind, s, value);
        result.start.update(start);
        result.end.update(end);
        return result;
    }
}

class UnaryNode : ASTNode {
    ASTNode operand;
    Location start;

    this(TokenKind kind, ASTNode operand) {
        this.kind = kind;
        this.operand = operand;
        start = null;
    }

    override string toString() {
        return format!"UnaryNode(%s, %s)"(kind, operand);
    }
}

class BinaryNode : ASTNode {
    ASTNode left;
    ASTNode right;

    this(TokenKind kind, ASTNode left, ASTNode right) {
        this.kind = kind;
        this.left = left;
        this.right = right;
    }

    override string toString() {
        return format!"BinaryNode(%s, %s, %s)"(kind, left, right);
    }
}

class SliceNode : ASTNode {
    ASTNode start;
    ASTNode stop;
    ASTNode step;

    this(ASTNode start, ASTNode stop, ASTNode step) {
        kind = TokenKind.Colon;
        this.start = start;
        this.stop = stop;
        this.step = step;
    }

    override string toString() {
        return format!"SliceNode(%s, %s, %s)"(start, stop, step);
    }
}

class ListNode : ASTNode {
    ASTNode[] elements;

    this(ASTNode[] elements) {
        kind = TokenKind.LeftBracket;
        this.elements = elements;
    }
}

alias KeyValue = Tuple!(Token, "key", ASTNode, "value");

class MappingNode : ASTNode {
    KeyValue[] elements;

    this(KeyValue[] elements) {
        kind = TokenKind.LeftCurly;
        this.elements = elements;
    }
}

class Parser {
    Tokenizer tokenizer;
    Token next;

    immutable static bool[TokenKind] expressionStarters;
    immutable static bool[TokenKind] valueStarters;
    immutable static bool[TokenKind] comparisonOperators;

    shared static this() {
        expressionStarters = [
            TokenKind.LeftCurly: true,
            TokenKind.LeftBracket: true,
            TokenKind.LeftParenthesis: true,
            TokenKind.At: true,
            TokenKind.Dollar: true,
            TokenKind.BackTick: true,
            TokenKind.Plus: true,
            TokenKind.Minus: true,
            TokenKind.BitwiseComplement: true,
            TokenKind.Integer: true,
            TokenKind.Float: true,
            TokenKind.Complex: true,
            TokenKind.True: true,
            TokenKind.False: true,
            TokenKind.None: true,
            TokenKind.Not: true,
            TokenKind.String: true,
            TokenKind.Word: true
        ];

        valueStarters = [
            TokenKind.Word: true,
            TokenKind.Integer: true,
            TokenKind.Float: true,
            TokenKind.Complex: true,
            TokenKind.String: true,
            TokenKind.BackTick: true,
            TokenKind.None: true,
            TokenKind.True: true,
            TokenKind.False: true
        ];

        comparisonOperators = [
            TokenKind.LessThan: true,
            TokenKind.LessThanOrEqual: true,
            TokenKind.GreaterThan: true,
            TokenKind.GreaterThanOrEqual: true,
            TokenKind.Equal: true,
            TokenKind.Unequal: true,
            TokenKind.AltUnequal: true,
            TokenKind.Is: true,
            TokenKind.In: true,
            TokenKind.Not: true
        ];
    }

    this(InputRange!(ubyte) r) {
        tokenizer = new Tokenizer(r);
        next = tokenizer.getToken();
    }

    @property
    public bool atEnd() {
        return next.kind == TokenKind.EOF;
    }

    private TokenKind advance() {
        next = tokenizer.getToken();
        return next.kind;
    }

    private Token expect(TokenKind kind) {
        if (next.kind != kind) {
            auto e = new ParserException(format!"expected %s but got %s"(kind, next.kind));

            e.location = next.start;
            throw e;
        }
        auto result = next;
        advance();
        return result;
    }

    private TokenKind consumeNewlines() {
        auto result = next.kind;

        while (result == TokenKind.Newline) {
            result = advance();
        }
        return result;
    }

    Token strings() {
        auto result = next;

        if (advance() == TokenKind.String) {
            string allText = "";
            string allValue = "";
            TokenKind kind;
            Location end;

            auto t = result.text;
            auto v = result.value.toString();
            auto start = result.start;

            do {
                allText ~= t;
                allValue ~= v;
                t = next.text;
                v = next.value.toString();
                end = next.end;
                kind = advance();
            } while (kind == TokenKind.String);
            allText ~= t; // the last one
            allValue ~= v;
            Variant av = allValue;
            result = new Token(TokenKind.String, allText, av);
            result.start = start;
            result.end = end;
        }
        return result;
    }

    ASTNode value() {
        auto kind = next.kind;
        Token t;

        if (kind !in valueStarters) {
            auto e = new ParserException(format!"unexpected when looking for value: %s"(kind));

            e.location = next.start;
            throw e;
        }

        if (kind == TokenKind.String) {
            t = strings();
        }
        else {
            t = new Token(next);
            advance();
        }
        return t;
    }

    ASTNode atom() {
        auto kind = next.kind;
        ASTNode result;

        switch (kind) {
        case TokenKind.LeftCurly:
            result = mapping();
            break;
        case TokenKind.LeftBracket:
            result = list();
            break;
        case TokenKind.LeftParenthesis:
            expect(TokenKind.LeftParenthesis);
            result = expr();
            expect(TokenKind.RightParenthesis);
            break;
        case TokenKind.Dollar:
            advance();
            expect(TokenKind.LeftCurly);
            auto spos = next.start;
            auto un = new UnaryNode(kind, primary());
            result = un;
            un.start = spos;
            expect(TokenKind.RightCurly);
            break;
        case TokenKind.Word:
        case TokenKind.Integer:
        case TokenKind.Float:
        case TokenKind.Complex:
        case TokenKind.String:
        case TokenKind.BackTick:
        case TokenKind.True:
        case TokenKind.False:
        case TokenKind.None:
            result = value();
            break;
        default:
            auto e = new ParserException(format!"unexpected: %s"(kind));

            e.location = next.start;
            throw e;
        }
        return result;
    }

    void invalidIndex(ulong n, Location loc) {
        auto e = new ParserException(format!"invalid index at %s: expected 1 expression, found %s"(loc, n));

        e.location = loc;
        throw e;
    }

    Tuple!(TokenKind, ASTNode) trailer() {
        auto kind = next.kind;
        ASTNode result = null;

        if (kind != TokenKind.LeftBracket) {
            expect(TokenKind.Dot);
            result = expect(TokenKind.Word);
        }
        else {
            auto isSlice = false;
            ASTNode startIndex = null;
            ASTNode stopIndex = null;
            ASTNode step = null;

            ASTNode getSliceElement() {
                Location loc = next.start;
                ListNode lb = listBody();
                ulong n = lb.elements.length;

                if (n != 1) {
                    invalidIndex(n, loc);
                }
                return lb.elements[0];
            }

            kind = advance();
            if (kind == TokenKind.Colon) {
                // it's a slice like [:xyz:abc]
                isSlice = true;
            }
            else {
                ASTNode elem = getSliceElement();

                kind = next.kind;
                if (kind != TokenKind.Colon) {
                    result = elem;
                }
                else {
                    startIndex = elem;
                    isSlice = true;
                }
            }
            if (!isSlice) {
                kind = TokenKind.LeftBracket;
            }
            else {
                // at this point startIndex is either null (if foo[:xyz]) or a
                // value representing the start. We are pointing at the COLON
                // after the start value
                kind = advance();
                if (kind == TokenKind.Colon) {  // no stop, but there might be a step
                    kind = advance();
                    if (kind != TokenKind.RightBracket) {
                        step = getSliceElement();
                    }
                }
                else if (kind != TokenKind.RightBracket) {
                    stopIndex = getSliceElement();
                    kind = next.kind;
                    if (kind == TokenKind.Colon) {
                        kind = advance();
                        if (kind != TokenKind.RightBracket) {
                            step = getSliceElement();
                        }
                    }
                }
                kind = TokenKind.Colon;  // to be returned
                result = new SliceNode(startIndex, stopIndex, step);
            }
            expect(TokenKind.RightBracket);
        }
        return tuple(kind, result);
    }

    ASTNode primary() {
        auto result = atom();

        while ((next.kind == TokenKind.Dot) || (next.kind == TokenKind.LeftBracket)) {
            auto p = trailer();
            result = new BinaryNode(p[0], result, p[1]);
        }
        return result;
    }

    Token objectKey() {
        Token result;

        if (next.kind == TokenKind.String) {
            result = strings();
        }
        else {
            result = next;
            advance();
        }
        return result;
    }

    ASTNode mappingBody() {
        KeyValue[] result = new KeyValue[0];
        auto kind = consumeNewlines();

        if ((kind != TokenKind.RightCurly) && (kind != TokenKind.EOF)) {
            if ((kind != TokenKind.Word) && (kind != TokenKind.String)) {
                auto e = new ParserException(format!"unexpected type for key: %s"(kind));

                e.location = next.start;
                throw e;
            }
            while ((kind == TokenKind.Word) || (kind == TokenKind.String)) {
                auto key = objectKey();

                kind = next.kind;

                if ((kind != TokenKind.Colon) && (kind != TokenKind.Assign)) {
                    auto e = new ParserException(format!"expected key-value separator, found: %s"(kind));

                    e.location = next.start;
                    throw e;
                }
                advance();
                consumeNewlines();
                result ~= KeyValue(key, expr());
                kind = next.kind;
                if ((kind == TokenKind.Newline) || (kind == TokenKind.Comma)) {
                    advance();
                    kind = consumeNewlines();
                }
                else if ((kind != TokenKind.RightCurly) && (kind != TokenKind.EOF)) {
                    auto e = new ParserException(format!"expected '}' or EOF, found: %s"(kind));

                    e.location = next.start;
                    throw e;
                }
            }
        }
        return new MappingNode(result);
    }

    ASTNode mapping() {
        expect(TokenKind.LeftCurly);
        auto result = mappingBody();
        expect(TokenKind.RightCurly);
        return result;
    }

    ListNode listBody() {
        ASTNode[] result = new ASTNode[0];
        auto kind = consumeNewlines();

        while (kind in expressionStarters) {
            result ~= expr();
            kind = next.kind;
            if ((kind != TokenKind.Newline) && (kind != TokenKind.Comma)) {
                break;
            }
            advance();
            kind = consumeNewlines();
        }
        return new ListNode(result);
    }

    ASTNode list() {
        expect(TokenKind.LeftBracket);
        auto result = listBody();
        expect(TokenKind.RightBracket);
        return result;
    }

    ASTNode container() {
        ASTNode result;
        TokenKind kind = consumeNewlines();

        if (kind == TokenKind.LeftCurly) {
            result = mapping();
        }
        else if (kind == TokenKind.LeftBracket) {
            result = list();
        }
        else if ((kind == TokenKind.Word) || (kind == TokenKind.String)) {
            result = mappingBody();
        }
        else {
            auto e = new ParserException(format!"unexpected type for container: %s"(kind));

            e.location = next.start;
            throw e;
        }
        consumeNewlines();
        return result;
    }

    ASTNode power() {
        auto result = primary();

        while (next.kind == TokenKind.Power) {
            advance();
            result = new BinaryNode(TokenKind.Power, result, unaryExpr());
        }
        return result;
    }

    ASTNode unaryExpr() {
        ASTNode result;
        auto kind = next.kind;

        if ((kind != TokenKind.Plus) && (kind != TokenKind.Minus) &&
            (kind != TokenKind.BitwiseComplement) && (kind != TokenKind.At)) {
            result = power();
        }
        else {
            advance();
            result = new UnaryNode(kind, unaryExpr());
        }
        return result;
    }

    ASTNode mulExpr() {
        auto result = unaryExpr();
        auto kind = next.kind;

        while ((kind == TokenKind.Star) || (kind == TokenKind.Slash) ||
                (kind == TokenKind.SlashSlash) || (kind == TokenKind.Modulo)) {
            advance();
            result = new BinaryNode(kind, result, unaryExpr());
            kind = next.kind;
        }
        return result;
    }

    ASTNode addExpr() {
        auto result = mulExpr();

        while ((next.kind == TokenKind.Plus) || (next.kind == TokenKind.Minus)) {
            auto op = next.kind;

            advance();
            result = new BinaryNode(op, result, mulExpr());
        }
        return result;
    }

    ASTNode shiftExpr() {
        auto result = addExpr();

        while ((next.kind == TokenKind.LeftShift) || (next.kind == TokenKind.RightShift)) {
            auto op = next.kind;

            advance();
            result = new BinaryNode(op, result, addExpr());
        }
        return result;
    }

    ASTNode bitandExpr() {
        auto result = shiftExpr();

        while (next.kind == TokenKind.BitwiseAnd) {
            advance();
            result = new BinaryNode(TokenKind.BitwiseAnd, result, shiftExpr());
        }
        return result;
    }

    ASTNode bitxorExpr() {
        auto result = bitandExpr();

        while (next.kind == TokenKind.BitwiseXor) {
            advance();
            result = new BinaryNode(TokenKind.BitwiseXor, result, bitandExpr());
        }
        return result;
    }

    ASTNode bitorExpr() {
        auto result = bitxorExpr();

        while (next.kind == TokenKind.BitwiseOr) {
            advance();
            result = new BinaryNode(TokenKind.BitwiseOr, result, bitxorExpr());
        }
        return result;
    }

    TokenKind compOp() {
        auto result = next.kind;
        auto shouldAdvance = false;

        advance();
        if ((result == TokenKind.Is) && (next.kind == TokenKind.Not)) {
            result = TokenKind.IsNot;
            shouldAdvance = true;
        }
        else if ((result == TokenKind.Not) && (next.kind == TokenKind.In)) {
            result = TokenKind.NotIn;
            shouldAdvance = true;
        }
        if (shouldAdvance) {
            advance();
        }
        return result;
    }

    ASTNode comparison() {
        auto result = bitorExpr();

        while (next.kind in comparisonOperators) {
            result = new BinaryNode(compOp(), result, bitorExpr());
        }
        return result;
    }

    ASTNode notExpr() {
        ASTNode result;

        if (next.kind != TokenKind.Not) {
            result = comparison();
        }
        else {
            advance();
            result = new UnaryNode(TokenKind.Not, notExpr());
        }
        return result;
    }

    ASTNode andExpr() {
        auto result = notExpr();

        while (next.kind == TokenKind.And) {
            advance();
            result = new BinaryNode(TokenKind.And, result, notExpr());
        }
        return result;
    }

    ASTNode expr() {
        auto result = andExpr();

        while (next.kind == TokenKind.Or) {
            advance();
            result = new BinaryNode(TokenKind.Or, result, andExpr());
        }
        return result;
    }
}

class ConfigException : Exception {
    this(string msg, string file = __FILE__, size_t line = __LINE__) {
        super(msg, file, line);
    }
}

class InvalidPathException : ConfigException {
    this(string msg, string file = __FILE__, size_t line = __LINE__) {
        super(msg, file, line);
    }
}

class BadIndexException : ConfigException {
    this(string msg, string file = __FILE__, size_t line = __LINE__) {
        super(msg, file, line);
    }
}

class CircularReferenceException : ConfigException {
    this(string msg, string file = __FILE__, size_t line = __LINE__) {
        super(msg, file, line);
    }
}

class DictWrapper {
    private Config config;
    private Variant[string] data;

    this(Config config) {
        this.config = config;
    }

    Variant baseGet(string k) {
        auto v = data[k];
        Variant result;

        if (v.peek!(ASTNode)) {
            ASTNode node = v.get!(ASTNode);

            if (auto mn = cast(MappingNode) node) {
                result = config.wrapMapping(mn);
            }
            else if (auto ln = cast(ListNode) node) {
                result = config.wrapList(ln);
            }
            else {
                result = v;
            }
        }
        //else if (v.peek!(ASTNode)) {
        //    result = config.evaluated(v.get!(ASTNode));
        //}
        else {
            result = v;
        }
        return result;
    }

    bool opBinaryRight(string op : "in")(string k) {
        return countUntil(data.keys, k) >= 0;
    }


    Variant[string] asDict() {
        Variant[string] result;

        foreach (k, v; data) {
            if (v.peek!(ASTNode)) {
                v = config.evaluated(v.get!(ASTNode));
            }
            if (v.peek!(DictWrapper)) {
                v = v.get!(DictWrapper).asDict();
            }
            else if (v.peek!(ListWrapper)) {
                v = v.get!(ListWrapper).asList();
            }
            result[k] = v;
        }
        return result;
    }
}

class ListWrapper {
    private Config config;
    private Variant[] data;

    this(Config config) {
        this.config = config;
    }

    Variant baseGet(int k) {
        auto v = data[k];
        Variant result;

        if (v.peek!(MappingNode)) {
            result = config.wrapMapping(v.get!(MappingNode));
        }
        else if (v.peek!(ListNode)) {
            result = config.wrapList(v.get!(ListNode));
        }
        else {
            result = v;
        }
        return result;
    }

    Variant[] asList() {
        Variant[] result = new Variant[data.length];

        foreach (i, v; data.enumerate()) {
            if (v.peek!(ASTNode)) {
                v = config.evaluated(v.get!(ASTNode));
            }
            else if (v.peek!(DictWrapper)) {
                v = v.get!(DictWrapper).asDict();
            }
            else if (v.peek!(ListWrapper)) {
                v = v.get!(ListWrapper).asList();
            }
            else {
                auto s = format!"%s"(v.type());
            }
            result[i] = v;
        }
        return result;
    }
}

alias PathElement  = Tuple!(TokenKind, "kind", ASTNode, "operand");

PathElement[] unpackPath(ASTNode node) {
    PathElement[] result = new PathElement[0];

    void visit(PathElement[] *path, ASTNode node) {
        if (auto t = cast(Token) node) {
            *path ~= PathElement(TokenKind.Dot, t);
        }
        else if (auto un = cast(UnaryNode) node) {
            visit(path, un.operand);
        }
        else if (auto bn = cast(BinaryNode) node) {
            visit(path, bn.left);
            if (bn.kind == TokenKind.Dot) {
                assert((cast(Token) bn.right) !is null);
            }
            *path ~= PathElement(bn.kind, bn.right);
        }
    }

    visit(&result, node);
    return result;
}

string toSource(ASTNode node) {
    string[] parts;
    auto path = unpackPath(node);

    foreach (i, elem; path.enumerate()) {
        if (elem.kind == TokenKind.Dot) {
            if (i > 0) {
                parts ~= ".";
            }
            parts ~= (cast(Token) elem.operand).text;
        }
        else if (elem.kind == TokenKind.LeftBracket) {
            parts ~= format!"[%s]"(toSource(elem.operand));
        }
        else {
            auto sn = cast(SliceNode) elem.operand;

            parts ~= "[";
            if (sn.start !is null) {
                parts ~= toSource(sn.start);
            }
            parts ~= ":";
            if (sn.stop !is null) {
                parts ~= toSource(sn.stop);
            }
            if (sn.step !is null) {
                parts ~= ":";
                parts ~= toSource(sn.step);
            }
            parts ~= "]";
        }
    }
    return parts.join("");
}

Complex!double toComplex(Variant v) {
    Complex!double result;

    if (v.peek!(Complex!double)) {
        result = v.get!(Complex!double);
    }
    else if (v.peek!double) {
        result = complex(v.get!(double), 0.0);
    }
    else if (v.peek!long) {
        result = complex(to!double(v.get!(long)), 0.0);
    }
    else {
        throw new ConfigException(format!"Cannot convert %s to complex"(v));
    }
    return result;
}

double toDouble(Variant v) {
    double result;

    if (v.peek!(double)) {
        result = v.get!(double);
    }
    else if (v.peek!long) {
        result = to!double(v.get!(long));
    }
    else {
        throw new ConfigException(format!"Cannot convert %s to double"(v));
    }
    return result;
}

bool isDict(Variant v) {
    return v.peek!(DictWrapper) || v.peek!(Variant[string]);
}

bool isList(Variant v) {
    return v.peek!(ListWrapper) || v.peek!(Variant[]);
}

Variant[string] asDict(Variant v) {
    if (v.peek!(Config))
        return v.get!(Config).data.asDict();
    if (v.peek!(DictWrapper))
        return v.get!(DictWrapper).asDict();
    return v.get!(Variant[string]);
}

Variant[] asList(Variant v) {
    return v.peek!(ListWrapper) ? v.get!(ListWrapper).asList() : v.get!(Variant[]);
}

class Evaluator {
    private Config config;
    private bool[UnaryNode] refsSeen;

    this(Config config) {
        this.config = config;
    }

    Variant evalAt(UnaryNode node) {
        auto fn = evaluate(node.operand).peek!(string);
        Variant result = null;

        if (fn is null) {
            throw new ConfigException("@ operand must be a string");
        }
        auto found = false;
        auto p = buildPath(config.rootDir, *fn);
        if (exists(p)) {
            found = true;
        }
        else {
            foreach (d; config.includePath) {
                p = buildPath(d, *fn);
                if (exists(p)) {
                    found = true;
                    break;
                }
            }
        }
        if (!found) {
            throw new ConfigException(format!"unable to locate %s"(fn));
        }
        auto f = File(p);
        auto r = inputRangeObject(f.byChunk(8192).joiner);
        auto parser = new Parser(r);
        auto cnode = parser.container();

        if (auto mn = cast(MappingNode) cnode) {
            auto cfg = new Config();

            cfg.noDuplicates = config.noDuplicates;
            cfg.strictConversions = config.strictConversions;
            cfg.context = config.context;
            cfg.cached = config.cached;
            cfg.parent = config;
            cfg.data = cfg.wrapMapping(mn);
            cfg.setPath(p);
            result = cfg;
        }
        else if (auto ln = cast(ListNode) cnode) {
            result = config.wrapList(ln);
        }
        else {
            result = cnode;
        }
        return result;
    }

    Variant evalReference(UnaryNode node) {
        return getFromPath(node.operand);
    }

    Variant negateNode(UnaryNode node) {
        Variant v = evaluate(node.operand);
        Variant result;

        if (v.peek!(long)) {
            result = -v.get!(long);
        }
        else if (v.peek!(double)) {
            result = -v.get!(double);
        }
        else if (v.peek!(Complex!double)) {
            result = -v.get!(Complex!double);
        }
        else {
            throw new ConfigException(format!"Unable to negate %s"(node));
        }
        return result;    }

    Variant[string] mergeDicts(Variant lhs, Variant rhs) {
        Variant[string] result = asDict(lhs);
        auto source = asDict(rhs);

        foreach (k, v; source) {
            if (k in result) {
                if (isDict(result[k]) && isDict(v)) {
                    v = mergeDicts(result[k], v);
                }
            }
            result[k] = v;
        }
        return result;
    }

    Variant evalAdd(BinaryNode node) {
        Variant lhs = evaluate(node.left);
        Variant rhs = evaluate(node.right);
        Variant result = null;

        if (isDict(lhs) && isDict(rhs)) {
            result = mergeDicts(lhs, rhs);
        }
        else if (isList(lhs) && isList(rhs)) {
            result = asList(lhs) ~ asList(rhs);
        }
        else if (lhs.peek!(string) && rhs.peek!(string)) {
            result = lhs.get!(string) ~ rhs.get!(string);
        }
        else if (lhs.peek!(Complex!double) || rhs.peek!(Complex!double)) {
            result = toComplex(lhs) + toComplex(rhs);
        }
        else if (lhs.peek!(double) || rhs.peek!(double)) {
            result = toDouble(lhs) + toDouble(rhs);
        }
        else if (lhs.peek!(long) && rhs.peek!(long)) {
            result = lhs.get!(long) + rhs.get!(long);
        }
        else {
            throw new ConfigException(format!"unable to add %s and %s"(lhs, rhs));
        }
        return result;
    }

    Variant evalSubtract(BinaryNode node) {
        Variant lhs = evaluate(node.left);
        Variant rhs = evaluate(node.right);
        Variant result = null;

        if (isDict(lhs) && isDict(rhs)) {
            auto lm = asDict(lhs);
            auto rm = asDict(rhs);

            foreach (k, v; rm) {
                if (k in lm) {
                    lm.remove(k);
                }
            }
            result = lm;
        }
        else if (lhs.peek!(Complex!double) || rhs.peek!(Complex!double)) {
            result = toComplex(lhs) - toComplex(rhs);
        }
        else if (lhs.peek!(double) || rhs.peek!(double)) {
            result = toDouble(lhs) - toDouble(rhs);
        }
        else if (lhs.peek!(long) && rhs.peek!(long)) {
            result = lhs.get!(long) - rhs.get!(long);
        }
        else {
            throw new ConfigException(format!"unable to subtract %s from %s"(rhs, lhs));
        }
        return result;
    }

    Variant evalMultiply(BinaryNode node) {
        Variant lhs = evaluate(node.left);
        Variant rhs = evaluate(node.right);
        Variant result = null;

        if (lhs.peek!(Complex!double) || rhs.peek!(Complex!double)) {
            result = toComplex(lhs) * toComplex(rhs);
        }
        else if (lhs.peek!(double) || rhs.peek!(double)) {
            result = toDouble(lhs) * toDouble(rhs);
        }
        else if (lhs.peek!(long) && rhs.peek!(long)) {
            result = lhs.get!(long) * rhs.get!(long);
        }
        else {
            throw new ConfigException(format!"unable to multiply %s by %s"(lhs, rhs));
        }
        return result;
    }

    Variant evalDivide(BinaryNode node) {
        Variant lhs = evaluate(node.left);
        Variant rhs = evaluate(node.right);
        Variant result = null;

        if (lhs.peek!(Complex!double) || rhs.peek!(Complex!double)) {
            result = toComplex(lhs) / toComplex(rhs);
        }
        else if (lhs.peek!(double) || rhs.peek!(double)) {
            result = toDouble(lhs) / toDouble(rhs);
        }
        else if (lhs.peek!(long) && rhs.peek!(long)) {
            result = to!double(lhs.get!(long)) / rhs.get!(long);
        }
        else {
            throw new ConfigException(format!"unable to divide %s by %s"(lhs, rhs));
        }
        return result;
    }

    Variant evalIntegerDivide(BinaryNode node) {
        Variant lhs = evaluate(node.left);
        Variant rhs = evaluate(node.right);
        Variant result = null;

        if (lhs.peek!(long) && rhs.peek!(long)) {
            result = lhs.get!(long) / rhs.get!(long);
        }
        else {
            throw new ConfigException(format!"unable to integer-divide %s by %s"(lhs, rhs));
        }
        return result;
    }

    Variant evalModulo(BinaryNode node) {
        Variant lhs = evaluate(node.left);
        Variant rhs = evaluate(node.right);
        Variant result = null;

        if (lhs.peek!(long) && rhs.peek!(long)) {
            result = lhs.get!(long) % rhs.get!(long);
        }
        else {
            throw new ConfigException(format!"unable to compute %s modulo %s"(lhs, rhs));
        }
        return result;
    }

    Variant evalPower(BinaryNode node) {
        Variant lhs = evaluate(node.left);
        Variant rhs = evaluate(node.right);
        Variant result = null;

        if (lhs.peek!(double) || rhs.peek!(double)) {
            result = pow(toDouble(lhs), toDouble(rhs));
        }
        else if (lhs.peek!(long) && rhs.peek!(long)) {
                result = pow(lhs.get!(long), rhs.get!(long));
            }
            else {
                throw new ConfigException(format!"unable to multiply %s by %s"(lhs, rhs));
            }
        return result;
    }

    Variant evalLeftShift(BinaryNode node) {
        Variant lhs = evaluate(node.left);
        Variant rhs = evaluate(node.right);
        Variant result = null;

        if (lhs.peek!(long) && rhs.peek!(long)) {
            result = lhs.get!(long) << rhs.get!(long);
        }
        else {
            throw new ConfigException(format!"unable to left-shift %s by %s"(lhs, rhs));
        }
        return result;
    }

    Variant evalRightShift(BinaryNode node) {
        Variant lhs = evaluate(node.left);
        Variant rhs = evaluate(node.right);
        Variant result = null;

        if (lhs.peek!(long) && rhs.peek!(long)) {
            result = lhs.get!(long) >> rhs.get!(long);
        }
        else {
            throw new ConfigException(format!"unable to right-shift %s by %s"(lhs, rhs));
        }
        return result;
    }

    Variant evalLogicalAnd(BinaryNode node) {
        Variant result;
        auto b = evaluate(node.left).get!(bool);

        if (!b) {
            result = b;
        }
        else {
            result = evaluate(node.right);
        }
        return result;
    }

    Variant evalLogicalOr(BinaryNode node) {
        Variant result;
        auto b = evaluate(node.left).get!(bool);

        if (b) {
            result = b;
        }
        else {
            result = evaluate(node.right);
        }
        return result;
    }

    Variant evalBitwiseOr(BinaryNode node) {
        Variant lhs = evaluate(node.left);
        Variant rhs = evaluate(node.right);
        Variant result = null;

        if (isDict(lhs) && isDict(rhs)) {
            result = mergeDicts(lhs, rhs);
        }
        else if (lhs.peek!(long) && rhs.peek!(long)) {
            result = lhs.get!(long) | rhs.get!(long);
        }
        else {
            throw new ConfigException(format!"unable to bitwise-or %s by %s"(lhs, rhs));
        }
        return result;
    }

    Variant evalBitwiseAnd(BinaryNode node) {
        Variant lhs = evaluate(node.left);
        Variant rhs = evaluate(node.right);
        Variant result = null;

        if (lhs.peek!(long) && rhs.peek!(long)) {
            result = lhs.get!(long) & rhs.get!(long);
        }
        else {
            throw new ConfigException(format!"unable to bitwise-and %s by %s"(lhs, rhs));
        }
        return result;
    }

    Variant evalBitwiseXor(BinaryNode node) {
        Variant lhs = evaluate(node.left);
        Variant rhs = evaluate(node.right);
        Variant result = null;

        if (lhs.peek!(long) && rhs.peek!(long)) {
            result = lhs.get!(long) ^ rhs.get!(long);
        }
        else {
            throw new ConfigException(format!"unable to bitwise-xor %s by %s"(lhs, rhs));
        }
        return result;
    }

    Variant evaluate(ASTNode node) {
        Variant result = null;

        //auto s = format!"%s"(node);
        if (auto t = cast(Token) node) {
            if (t.kind == TokenKind.Word) {
                if (config.context is null) {
                    throw new ConfigException("no context provided");
                }
                else if (t.text !in config.context) {
                    throw new ConfigException(format!"unknown variable '%s'"(t.text));
                }
                else {
                    result = config.context[t.text];
                }
            }
            else if (t.kind != TokenKind.BackTick) {
                result = t.value;
            }
            else {
                result = config.convertString(t.value.get!(string));
            }
        }
        else if (auto ln = cast(ListNode) node) {
            result = config.wrapList(ln).asList();
        }
        else if (auto mn = cast(MappingNode) node) {
            result = config.wrapMapping(mn).asDict();
        }
        else if (auto un = cast(UnaryNode) node) {
            switch (un.kind) {
            case TokenKind.At:
                result = evalAt(un);
                break;
            case TokenKind.Dollar:
                result = evalReference(un);
                break;
            case TokenKind.Minus:
                result = negateNode(un);
                break;
            default:
                throw new ConfigException(format!"Unable to evaluate %s"(un));
            }
        }
        else if (auto bn = cast(BinaryNode) node) {
            switch (bn.kind) {
            case TokenKind.Plus:
                result = evalAdd(bn);
                break;
            case TokenKind.Minus:
                result = evalSubtract(bn);
                break;
            case TokenKind.Star:
                result = evalMultiply(bn);
                break;
            case TokenKind.Slash:
                result = evalDivide(bn);
                break;
            case TokenKind.SlashSlash:
                result = evalIntegerDivide(bn);
                break;
            case TokenKind.Modulo:
                result = evalModulo(bn);
                break;
            case TokenKind.Power:
                result = evalPower(bn);
                break;
            case TokenKind.LeftShift:
                result = evalLeftShift(bn);
                break;
            case TokenKind.RightShift:
                result = evalRightShift(bn);
                break;
            case TokenKind.And:
                result = evalLogicalAnd(bn);
                break;
            case TokenKind.Or:
                result = evalLogicalOr(bn);
                break;
            case TokenKind.BitwiseAnd:
                result = evalBitwiseAnd(bn);
                break;
            case TokenKind.BitwiseOr:
                result = evalBitwiseOr(bn);
                break;
            case TokenKind.BitwiseXor:
                result = evalBitwiseXor(bn);
                break;
            default:
                throw new ConfigException(format!"Unable to evaluate %s"(bn));
            }
        }
        return result;
    }

    Variant[] getSlice(Variant source, SliceNode sn) {
        ulong len = source.peek!(ListWrapper) ? source.get!(ListWrapper).data.length : source.get!(Variant[]).length;
        int size = to!int(len);
        int start, stop, step;

        if (sn.step is null) {
            step = 1;
        }
        else {
            step = to!int(evaluate(sn.step).get!(long));
        }
        if (step == 0) {
            throw new ConfigException("slice step cannot be zero");
        }
        if (sn.start is null) {
            start = 0;
        }
        else {
            start = to!int(evaluate(sn.start).get!(long));
            if (start < 0) {
                if (start >= -size) {
                    start += size;
                }
                else {
                    start = 0;
                }
            }
            else if (start >= size) {
                start = size - 1;
            }
        }
        if (sn.stop is null) {
            stop = size - 1;
        }
        else {
            stop = to!int(evaluate(sn.stop).get!(long));
            if (stop < 0) {
                if (stop >= -size) {
                    stop += size;
                }
                else {
                    stop = 0;
                }
            }
            if (stop > size) {
                stop = size;
            }
            if (step < 0) {
                stop++;
            }
            else {
                stop--;
            }
        }
        if ((step < 0) && (start < stop)) {
            auto tmp = stop;

            stop = start;
            start = tmp;
        }
        Variant[] result;
        auto i = start;
        auto notDone = (step > 0) ? i <= stop : i >= stop;
        auto j = 0;
        while (notDone) {
            auto elem = source.peek!(ListWrapper) ? source.get!(ListWrapper).data[i] : source.get!(Variant[])[i];
            result ~= elem;
            i += step;
            notDone = (step > 0) ? i <= stop : i >= stop;
        }
        return result;
    }

    Variant getFromPath(ASTNode node) {
        auto parts = unpackPath(node);
        auto currentConfig = config;
        auto currentEvaluator = this;
        Variant result = config;

        //writeln(format!"GFP: %s: %s"(config, toSource(node)));

        for (int i = 0; i < parts.length; i++) {
            auto elem = parts[i];
            auto sn = cast(SliceNode) elem.operand;
            Variant operand;

            // compute the index based on the path element.
            // slices are handled later.
            if (sn is null) {
                if (elem.kind == TokenKind.Dot) {
                    auto t = cast(Token) elem.operand;

                    assert(t !is null);
                    operand = t.text;
                }
                else {
                    auto an = cast(ASTNode) elem.operand;

                    assert(an !is null);
                    operand = currentEvaluator.evaluate(an);
                }
                if (isDict(result) || result.peek!(Config)) {
                    if (!operand.peek!(string)) {
                        throw new BadIndexException(format!"string required, but found %s"(operand));
                    }
                    string k = operand.get!(string);
                    //writeln(format!"%d key = %s"(i, k));
                    if (result.peek!(Config)) {
                        auto c = result.get!(Config);

                        if (k !in c.data.data) {
                            throw new ConfigException(format!"not found in configuration: %s"(k));
                        }
                        currentConfig = c;
                        result = c.data.baseGet(k);
                        currentEvaluator = c.evaluator;
                    }
                    else if (result.peek!(DictWrapper)) {
                        auto dw = result.get!(DictWrapper);

                        if (k !in dw.data) {
                            throw new ConfigException(format!"not found in configuration: %s"(k));
                        }
                        result = dw.baseGet(k);
                    }
                    else {
                        auto d = result.get!(Variant[string]);


                        result = d[k];
                    }
                }
                else if (isList(result)) {
                    int index;

                    if (!operand.peek!(long)) {
                        throw new BadIndexException("invalid list operand");
                    }
                    index = to!int(operand.get!(long));
                    ulong len = result.peek!(ListWrapper) ? result.get!(ListWrapper).data.length : result.get!(Variant[]).length;
                    int n = to!int(len);

                    if (index < 0) {
                        if (index >= -n) {
                            index += n;
                        }
                    }
                    if ((index < 0) || (index >= n)) {
                        throw new BadIndexException("index out of range");
                    }
                    if (result.peek!(ListWrapper)) {
                        result = result.get!(ListWrapper).data[index];
                    }
                    else {
                        result = result.get!(Variant[])[index];
                    }
                }
                else {
                    auto msg = format!"unhandled case: %s / %s"(result, operand);
                    throw new ConfigException(msg);
                }
            }
            else {
                // handle slices
                if (!isList(result)) {
                    throw new BadIndexException("slices can only operate on lists");
                }
                if (result.peek!(ListWrapper)) {
                    result = result.get!(ListWrapper).asList();
                }
                result = getSlice(result, sn);
            }
            if (result.peek!(ASTNode)) {
                auto rn = result.get!(ASTNode);

                if (rn.kind == TokenKind.Dollar) {
                    //auto ds = format!"%s:%s"(currentEvaluator.config.path, currentEvaluator.refsSeen);
                    auto urn = cast(UnaryNode) rn;
                    if (urn in currentEvaluator.refsSeen) {
                        string[] p;

                        foreach (k, v; currentEvaluator.refsSeen) {
                            auto s = format!"%s %s"(toSource(k), k.start);

                            p ~= s;
                        }
                        p.sort();
                        auto msg = format!"Circular reference: %s"(p.join(", "));
                        throw new CircularReferenceException(msg);
                    }
                    currentEvaluator.refsSeen[urn] = true;
                    //ds = format!"%s:%s"(currentEvaluator.config.path, currentEvaluator.refsSeen);
                    //writeln(ds);
                }
                result = currentEvaluator.evaluate(rn);
            }
            //writeln(format!"%d res = %s"(i, result));
        }
        refsSeen.clear();
        //writeln(format!"%s -> %s"(toSource(node), result));
        return result;
    }
}

private static Regex!char IDENTIFIER_PATTERN = regex(r"^(?!\d)(\w+)$");

bool isIdentifier(string s) {
    return !matchFirst(s, IDENTIFIER_PATTERN).empty;
}

ASTNode parsePath(string s) {
    auto r = inputRangeObject(s.representation.map!(b => ubyte(b)));
    Parser parser;

    try {
        parser = new Parser(r);
    }
    catch (RecognizerException e) {
        throw new InvalidPathException(format!"Invalid path: %s"(s));
    }
    if (parser.next.kind != TokenKind.Word) {
        throw new InvalidPathException(format!"Invalid path: %s"(s));
    }
    try {
        auto result = parser.primary();

        if (!parser.atEnd) {
            throw new InvalidPathException(format!"Invalid path: %s"(s));
        }
        return result;
    }
    catch (TokenizerException te) {
        auto e = new InvalidPathException(format!"Invalid path: %s"(s));
        e.next = te;
        throw e;
    }
}

Variant unwrap(Variant o) {
    Variant result = o;

    if (o.peek!(DictWrapper)) {
        result = o.get!(DictWrapper).asDict();
    }
    else if (o.peek!(ListWrapper)) {
        result = o.get!(ListWrapper).asList();
    }
    return result;
}

private static Regex!char ISO_DATETIME_PATTERN = regex(r"^(\d{4})-(\d{2})-(\d{2})(([ T])(((\d{2}):(\d{2}):(\d{2}))(\.\d{1,6})?(([+-])(\d{2}):(\d{2})(:(\d{2})(\.\d{1,6})?)?)?))?$");
private static Regex!char ENV_VALUE_PATTERN = regex(r"^\$(\w+)(\|(.*))?$");

Variant defaultStringConverter(string s) {
    Variant result = s;
    auto c = matchFirst(s, ISO_DATETIME_PATTERN);

    if (!c.empty) {
        int year = to!int(c[1]);
        int month = to!int(c[2]);
        int day = to!int(c[3]);
        auto hasTime = c[5].length > 0;

        if (!hasTime) {
            result = Date(year, month, day);
        }
        else {
            int hour = to!int(c[8]);
            int minute = to!int(c[9]);
            int second = to!int(c[10]);
            int nanos = 0;

            if (c[11].length > 0) {
                nanos = to!int(to!double(c[11]) * 1.0e9);
            }
            auto hasOffset = c[13].length > 0;

            if (!hasOffset) {
                auto dt = DateTime(year, month, day, hour, minute, second);
                auto dur = nsecs(nanos);
                result = SysTime(dt, dur);
            }
            else {
                int ohour = to!int(c[14]);
                int ominute = to!int(c[15]);
                int osecond = (c[17].length > 0) ? to!int(c[17]) : 0;

                auto dur = minutes(ominute + ohour * 60);
                auto tz = new SimpleTimeZone(dur);
                dur = nsecs(nanos);
                auto dt = DateTime(year, month, day, hour, minute, second);
                result = dt;
                result = SysTime(dt, dur, cast(immutable(TimeZone)) tz);
            }
        }
    }
    else {
        c = matchFirst(s, ENV_VALUE_PATTERN);
        if (!c.empty) {
            auto varName = c[1];
            auto hasPipe = c[2].length > 0;
            auto dv = hasPipe ? c[3] : null;

            result = environment.get(varName, dv);
        }
    }
    return result;
}

class Config {
    bool noDuplicates = true;
    bool strictConversions = true;
    string path;
    string rootDir;
    string[] includePath;
    Config parent;
    Variant[string] context;
    private Variant[string] cache;
    private DictWrapper data;
    private bool _cached;
    private Evaluator evaluator;
    Variant function(string) converter;

    private static Variant MISSING;

    static this() {
        MISSING = new Object();
    }

    override string toString() {
        return format!"Config(%s)"(baseName(path));
    }

    @property
    bool cached() {
        return _cached;
    }

    @property
    void cached(bool value) {
        _cached = value;
        if (!value) {
            cache.clear();
        }
    }

    this() {
        includePath = new string[0];
        evaluator = new Evaluator(this);
        converter = &defaultStringConverter;
        //writeln(format!"cfg = %s(%s) eval = %s(%s)"(this, cast(void *) this, evaluator, cast(void *) evaluator));
    }

    this(InputRange!(ubyte) r) {
        this();
        load(r);
    }

    this(string path) {
        this();
        loadFile(path);
    }

    void load(InputRange!(ubyte) r) {
        auto parser = new Parser(r);
        auto node = parser.container();
        auto mn = cast(MappingNode) node;

        if (mn is null){
            throw new ConfigException("Root configuration must be a mapping.");
        }
        data = wrapMapping(mn);
        cache.clear();
    }

    private void setPath(string path) {
        auto p = absolutePath(path);
        this.path = p;
        rootDir = dirName(p);
    }

    DictWrapper wrapMapping(MappingNode node) {
        DictWrapper result = new DictWrapper(this);
        Location[string] seen;

        foreach (entry; node.elements) {
            auto t = entry.key;
            string k = (t.kind == TokenKind.Word) ? t.text: t.value.get!(string);

            if (noDuplicates) {
                if (k in seen) {
                    auto msg = format!"Duplicate key %s seen at %s (previously %s)"(k, t.start, seen[k]);
                    throw new ConfigException(msg);
                }
                seen[k] = t.start;
            }
            result.data[k] = entry.value;
        }
        return result;
    }

    ListWrapper wrapList(ListNode node) {
        ListWrapper result = new ListWrapper(this);

        foreach (e; node.elements) {
            Variant v = e;
            result.data ~= v;
        }
        return result;
    }

    void loadFile(string path) {
        auto f = File(path);
        auto r = inputRangeObject(f.byChunk(8192).joiner);
        load(r);
        setPath(path);
    }

    Variant evaluated(ASTNode node) {
        Variant result = evaluator.evaluate(node);

        return result;
    }

    Variant getFromPath(string key) {
        evaluator.refsSeen.clear();
        return evaluator.getFromPath(parsePath(key));
    }

    Variant baseGet(string key, Variant defaultValue = MISSING) {
        Variant result = null;

        if (cached && key in cache) {
            result = cache[key];
        }
        else if (data is null) {
            throw new ConfigException("No data in configuration");
        }
        else {
            auto found = false;

            if (key in data.data) {
                result = data.data[key];
                if (result.peek!(ASTNode)) {
                    result = evaluated(result.get!(ASTNode));
                }
                found = true;
            }
            else if (!isIdentifier(key)) {
                // Treat as a path
                try {
                    result = getFromPath(key);
                    found = true;
                }
                catch (InvalidPathException ipe) {
                    throw ipe;
                }
                catch (BadIndexException bie) {
                    throw bie;
                }
                catch (CircularReferenceException cre) {
                    throw cre;
                }
                catch (ConfigException ce) {
                }
            }
            if (!found) {
                if (defaultValue == MISSING) {
                    throw new ConfigException(format!"Not found in configuration: %s"(key));
                }
                result = defaultValue;
            }
            if (cached) {
                cache[key] = result;
            }
        }
        return result;
    }

    Variant get(string key, Variant defaultValue = MISSING) {
        return unwrap(baseGet(key, defaultValue));
    }

    Variant opIndex(string key) {
        return get(key);
    }

    bool opBinaryRight(string op : "in")(string k) {
        return k in data;
    }

    Variant convertString(string s) {
        Variant result = converter(s);

        if ((result == s) && strictConversions) {
            throw new ConfigException(format!"unable to convert '%s'"(s));
        }
        return result;
    }
}
