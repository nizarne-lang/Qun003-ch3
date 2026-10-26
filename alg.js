/* ============== محرّك جبري مصغّر لتصحيح إجابات كثيرات الحدود والمقادير النسبية ==============
   يحوّل ما يكتبه الطالب إلى دالة كسرية (بسط/مقام) على حلقة كثيرات الحدود ذات المعاملات
   النسبية، ثم يقارنها بالإجابة المخزّنة بالضرب التبادلي. فيُقبل أي شكل مكافئ جبرياً:
     (x-1)(x+1)  =  x^2-1 ،  2/(x-2) = -2/(2-x) ،  0.5x = x/2.
   وللأسئلة التي تطلب «التحليل» نحسب أيضاً عدد العوامل غير الثابتة في المستوى الأعلى،
   فلا يُقبل مقدار مفكوك بدل مقدار محلَّل.
   ملاحظة: الجذور العددية تُعامل كمتغيّرات رمزية مع القاعدة (√k)² = k ، فيصح
     (√2 x + y)(√2 x - y) = 2x² - y².
   ======================================================================================= */
(function () {
  'use strict';

  /* ---------------- أعداد نسبية ---------------- */
  function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { var t = a % b; a = b; b = t; } return a || 1; }
  function R(n, d) {
    if (d === undefined) d = 1;
    if (d === 0) throw new Error('÷0');
    if (d < 0) { n = -n; d = -d; }
    var g = gcd(n, d);
    return { n: n / g, d: d / g };
  }
  function radd(a, b) { return R(a.n * b.d + b.n * a.d, a.d * b.d); }
  function rmul(a, b) { return R(a.n * b.n, a.d * b.d); }
  function rneg(a) { return { n: -a.n, d: a.d }; }
  function rz(a) { return a.n === 0; }
  var ONE = R(1);

  /* ---------------- حدوديات متعدّدة المتغيّرات ----------------
     المفتاح: "x^2*y" مرتَّب أبجدياً ، والثابت مفتاحه "" */
  function keyMon(k) {
    var m = {};
    if (!k) return m;
    k.split('*').forEach(function (p) {
      var i = p.lastIndexOf('^');
      m[p.slice(0, i)] = parseInt(p.slice(i + 1), 10);
    });
    return m;
  }
  function monKey(m) {
    var ks = Object.keys(m).filter(function (k) { return m[k] !== 0; }).sort();
    return ks.map(function (k) { return k + '^' + m[k]; }).join('*');
  }
  // ضرب أحاديتين مع تبسيط (√k)² = k
  function monMul(m1, m2) {
    var m = {}, c = ONE, k;
    for (k in m1) m[k] = (m[k] || 0) + m1[k];
    for (k in m2) m[k] = (m[k] || 0) + m2[k];
    for (k in m) {
      if (k.charAt(0) === '√' && /^\d+$/.test(k.slice(1))) {
        var rad = parseInt(k.slice(1), 10), e = m[k];
        var q = Math.floor(e / 2);
        if (q > 0) c = rmul(c, R(Math.pow(rad, q)));
        m[k] = e - 2 * q;
      }
      if (m[k] === 0) delete m[k];
    }
    return { m: m, c: c };
  }
  function pConst(r) { var o = {}; if (!rz(r)) o[''] = r; return o; }
  function pVar(v) { var o = {}; o[v + '^1'] = ONE; return o; }
  function pAdd(a, b) {
    var o = {}, k;
    for (k in a) o[k] = a[k];
    for (k in b) { o[k] = o[k] ? radd(o[k], b[k]) : b[k]; if (rz(o[k])) delete o[k]; }
    return o;
  }
  function pNeg(a) { var o = {}; for (var k in a) o[k] = rneg(a[k]); return o; }
  function pMul(a, b) {
    var o = {}, ka, kb;
    for (ka in a) for (kb in b) {
      var mm = monMul(keyMon(ka), keyMon(kb));
      var c = rmul(rmul(a[ka], b[kb]), mm.c);
      var k = monKey(mm.m);
      o[k] = o[k] ? radd(o[k], c) : c;
      if (rz(o[k])) delete o[k];
    }
    return o;
  }
  function pPow(a, e) { var r = pConst(ONE); for (var i = 0; i < e; i++) r = pMul(r, a); return r; }
  function pZero(a) { return Object.keys(a).length === 0; }
  function pIsConst(a) { var ks = Object.keys(a); return ks.length === 0 || (ks.length === 1 && ks[0] === ''); }

  /* ---------------- دوال كسرية ---------------- */
  function F(n, d) { return { n: n, d: d || pConst(ONE) }; }
  function fAdd(a, b) { return F(pAdd(pMul(a.n, b.d), pMul(b.n, a.d)), pMul(a.d, b.d)); }
  function fNeg(a) { return F(pNeg(a.n), a.d); }
  function fMul(a, b) { return F(pMul(a.n, b.n), pMul(a.d, b.d)); }
  function fDiv(a, b) { if (pZero(b.n)) throw new Error('÷0'); return F(pMul(a.n, b.d), pMul(a.d, b.n)); }
  function fPow(a, e) { if (e < 0) return fPow(F(a.d, a.n), -e); return F(pPow(a.n, e), pPow(a.d, e)); }
  function fConstQ(a) { return pIsConst(a.n) && pIsConst(a.d); }

  /* ---------------- تهيئة النص ---------------- */
  var ARD = { '٠': '0', '١': '1', '٢': '2', '٣': '3', '٤': '4', '٥': '5', '٦': '6', '٧': '7', '٨': '8', '٩': '9' };
  var SUP = { '⁰': '0', '¹': '1', '²': '2', '³': '3', '⁴': '4', '⁵': '5', '⁶': '6', '⁷': '7', '⁸': '8', '⁹': '9', '⁻': '-', '⁺': '+' };

  function prep(s) {
    var t = String(s == null ? '' : s);
    t = t.replace(/[٠-٩]/g, function (d) { return ARD[d]; });
    t = t.replace(/[⁰¹²³⁴-⁹⁺⁻]/g, function (c) { return '^' + SUP[c]; });
    t = t.replace(/\^(-?)\^/g, function (m0, g) { return '^' + g; });
    for (var i = 0; i < 5; i++) t = t.replace(/\^(-?\d+)\^(\d)/g, '^$1$2');
    t = t.replace(/[×⋅·∙٭]/g, '*');
    t = t.replace(/[÷]/g, '/');
    t = t.replace(/[−–—―]/g, '-');
    t = t.replace(/[​-‏‪-‮⁦-⁩﻿]/g, '');
    t = t.replace(/\s+/g, '');
    t = t.replace(/[\[\{]/g, '(').replace(/[\]\}]/g, ')');
    t = t.toLowerCase();
    t = t.replace(/sqrt/g, '#').replace(/√/g, '#');
    // إزالة بادئة مثل  f(x)=  أو  p(x,y)=
    t = t.replace(/^[a-z](\([a-z,]*\))?=/, '');
    t = t.replace(/[.،,;؛]+$/, '');
    return t;
  }

  /* ---------------- محلّل نحوي ---------------- */
  function Parser(src) {
    this.s = src; this.i = 0; this.scope = 0;
    this.hasSum = false; this.top = []; this.lastExp = 1;
  }
  Parser.prototype.peek = function () { return this.s.charAt(this.i); };
  Parser.prototype.eof = function () { return this.i >= this.s.length; };
  function isD(c) { return c >= '0' && c <= '9'; }
  function isA(c) { return (c >= 'a' && c <= 'z') || c === 'π'; }
  function startsAtom(c) { return isD(c) || isA(c) || c === '(' || c === '#' || c === '.'; }

  Parser.prototype.expr = function () {
    var v = this.term();
    while (!this.eof()) {
      var c = this.peek();
      if (c === '+') { this.i++; if (this.scope === 0) this.hasSum = true; v = fAdd(v, this.term()); }
      else if (c === '-') { this.i++; if (this.scope === 0) this.hasSum = true; v = fAdd(v, fNeg(this.term())); }
      else break;
    }
    return v;
  };
  Parser.prototype.term = function () {
    var top = (this.scope === 0);
    var v = this.unary();
    if (top) this.top.push({ v: v, e: this.lastExp });
    while (!this.eof()) {
      var c = this.peek(), u;
      if (c === '*') { this.i++; u = this.unary(); if (top) this.top.push({ v: u, e: this.lastExp }); v = fMul(v, u); }
      else if (c === '/') { this.i++; u = this.unary(); if (top) this.top.push({ v: u, e: 0 }); v = fDiv(v, u); }
      else if (startsAtom(c)) { u = this.unary(); if (top) this.top.push({ v: u, e: this.lastExp }); v = fMul(v, u); }
      else break;
    }
    return v;
  };
  Parser.prototype.unary = function () {
    if (this.peek() === '-') { this.i++; return fNeg(this.unary()); }
    if (this.peek() === '+') { this.i++; return this.unary(); }
    return this.power();
  };
  Parser.prototype.power = function () {
    var b = this.atom();
    this.lastExp = 1;
    if (this.peek() === '^') {
      this.i++;
      var e = this.exponent();
      b = fPow(b, e);
      this.lastExp = e > 0 ? e : 1;
    }
    return b;
  };
  Parser.prototype.exponent = function () {
    var sg = 1;
    if (this.peek() === '-') { this.i++; sg = -1; }
    else if (this.peek() === '+') this.i++;
    var d = '', par = false;
    if (this.peek() === '(') { this.i++; par = true; if (this.peek() === '-') { this.i++; sg = -sg; } }
    while (isD(this.peek())) d += this.s.charAt(this.i++);
    if (par && this.peek() === ')') this.i++;
    if (!d) throw new Error('أس غير صحيح');
    return sg * parseInt(d, 10);
  };
  Parser.prototype.atom = function () {
    var c = this.peek();
    if (c === '(') {
      this.i++; this.scope++;
      var v = this.expr();
      this.scope--;
      if (this.peek() !== ')') throw new Error('أقواس غير متوازنة');
      this.i++;
      return v;
    }
    if (c === '#') {
      this.i++;
      if (this.peek() === '(') {
        this.i++;
        var st = this.i, dep = 1;
        while (this.i < this.s.length && dep > 0) {
          var ch = this.s.charAt(this.i);
          if (ch === '(') dep++;
          if (ch === ')') dep--;
          this.i++;
        }
        return radicalOf(this.s.slice(st, this.i - 1));
      }
      var t = '';
      while (isD(this.peek())) t += this.s.charAt(this.i++);
      if (t) return radicalOf(t);
      if (isA(this.peek())) return radicalOf(this.s.charAt(this.i++));
      throw new Error('جذر غير مكتمل');
    }
    if (isD(c) || c === '.') {
      var n = '';
      while (isD(this.peek()) || this.peek() === '.') n += this.s.charAt(this.i++);
      if (n.indexOf('.') >= 0) {
        var pr = n.split('.'), dec = pr[1] || '';
        return F(pConst(R(parseInt((pr[0] || '0') + dec, 10), Math.pow(10, dec.length))));
      }
      return F(pConst(R(parseInt(n, 10))));
    }
    if (isA(c)) { this.i++; return F(pVar(c)); }
    throw new Error('رمز غير متوقع: ' + c);
  };
  function radicalOf(inner) {
    if (/^\d+$/.test(inner)) {
      var n = parseInt(inner, 10), out = 1, k = 2;
      if (n === 0) return F(pConst(R(0)));
      while (k * k <= n) { while (n % (k * k) === 0) { out *= k; n /= k * k; } k++; }
      if (n === 1) return F(pConst(R(out)));
      return fMul(F(pConst(R(out))), F(pVar('√' + n)));
    }
    return F(pVar('√(' + inner + ')'));
  }

  /* ---------------- الواجهة ---------------- */
  function parse(s) {
    var t = prep(s);
    if (t === '') throw new Error('فارغ');
    var p = new Parser(t);
    var v = p.expr();
    if (!p.eof()) throw new Error('بقية غير مفهومة: ' + t.slice(p.i));
    return { v: v, p: p };
  }

  function val(s) { return parse(s).v; }

  function eq(a, b) {
    try {
      var x = val(a), y = val(b);
      return pZero(pAdd(pMul(x.n, y.d), pNeg(pMul(y.n, x.d))));
    } catch (e) { return false; }
  }

  // عدد العوامل غير الثابتة في المستوى الأعلى (0 إذا كان المقدار مجموعاً، أي غير محلَّل)
  function nfactors(s) {
    try {
      var r = parse(s);
      if (r.p.hasSum) return 0;
      var c = 0;
      r.p.top.forEach(function (f) { if (!fConstQ(f.v)) c += f.e; });
      return c;
    } catch (e) { return 0; }
  }

  function eqFact(a, b) {
    if (!eq(a, b)) return false;
    var need = nfactors(b);
    if (need <= 1) return nfactors(a) >= need;
    return nfactors(a) >= need;
  }

  window.ALG = { eq: eq, eqFact: eqFact, nfactors: nfactors, parse: parse, prep: prep };
})();
