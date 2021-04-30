use "ponytest"
use "itertools"
use "collections"

/* TODO
 * headers from http are not stored case-insensitively, so we cannot
 * easily disambiguate them
 * the path /foo//.. -> / stuff isn't performed for us
 */

use "http"
use "crypto"

// the means by which we sign requests
primitive DigestUnsigned
  """
  s3 payloads are unsigned
  """
  fun name(): String => "UNSIGNED-PAYLOAD"
  fun digest(s: String): String => "UNSIGNED-PAYLOAD"
primitive Digest256
  fun name(): String => "AWS4-HMAC-SHA256"
  fun digest(s: String): String => ToHexString(SHA256(s))
primitive Digest512
  fun name(): String => "AWS4-HMAC-SHA512"
  fun digest(s: String): String => ToHexString(SHA512(s))
type SigningAlgo is (Digest256 | Digest512 | DigestUnsigned)


class val _KV
  """
  a key/value pair that represents a header or query string
  component so that we can sort it in an array
  """
  let _data: (String, (String | None))
  new val create(name': String, value': (String | None)) =>
    _data = (name', value')
  fun name(): String val => _data._1
  fun value(): (String val | None) => _data._2
  fun sort_value(): String val =>
    match this.value()
    | None => ""
    | let s: String => s
    end

  fun lt(that: _KV): Bool val => this.name().lt(that.name())
  fun gt(that: _KV): Bool val => this.name().gt(that.name())
  fun eq(that: _KV): Bool val =>
    // TODO: am i really going to sort headers by value, too,
    // so that i don't need a separate type for query string components?
    if this.name().eq(that.name()) then
      this.sort_value().eq(that.sort_value())
    else
      false
    end
  fun ne(that: _KV): Bool val => this.eq(that) == false
  fun le(that: _KV): Bool val => this.lt(that) or this.eq(that)
  fun ge(that: _KV): Bool val => this.gt(that) or this.eq(that)
  fun compare(that: _KV): (Less val | Equal val | Greater val) =>
    if this.eq(that) then
      Equal
    elseif this.lt(that) then
      Less
    else
      Greater
    end

class iso SigV4
  let _url: URL val
  let _method: String val
  let _algo: SigningAlgo val
  let _passes: U8 val
  let _headers: Array[_KV] ref
  let _service: String val
  let _payload: String val

  /* TODO
   * maybe we should accept the path separately from the url itself
   * because it might not be valid from the perspective of pony's http.URL.
   * does the http package care about //? -- no, no it does not.
   */
  new create(method: String, url: URL, headers: Map[String, String],
             service: String = "S3", algo: SigningAlgo = Digest256,
             payload: String = "") ? =>
    _method = method
    _url = url
    _algo = algo
    _payload = payload

    _service = service.lower()
    _passes = if service == "s3" then 2 else 1 end

    // convert the headers map into an array of (header, value)
    _headers = _convert_headers(headers)

    // assert that the host or :authority header was supplied
    let found: (_KV | None) =
      for header in _headers.values() do
        if ["host"; ":authority"].contains(header.name()) then
          break header
        end
      end
    if found is None then
      error
    end

  fun tag _convert_headers(headers: Map[String, String]): Array[_KV] ref =>
    """
    convert a headers map into a sorted array of (header, value) pairs.
    note that the headers from the http package are currently broken
    because multiple values are joined into a single string and separated
    by ", ". rather than parse this garbage, we leave it to the user to
    supply valid input -- multiple values for a header should be delimited
    by a single "," only.
    """
    let h = Array[_KV](headers.size())
    for (k, value) in headers.pairs() do
      let v = value.clone()
      v.strip()
      v.replace("  ", " ")
      h.push(_KV(k.lower(), consume v))
    end
    Sort[Array[_KV], _KV](h)

  fun _encoded_segment(segment: String, passes: U8): String val ? =>
    """
    URL-encode a single path segment some number of times
    """
    if passes == 0 then
      segment
    elseif segment == "" then
      segment
    else
      let segment' = _encoded_segment(segment, passes - 1)?
      URLEncode.encode(segment', URLPartPath, false)?
    end

  fun _encoded_path(path: String, passes: U8): String val ? =>
    """
    compose the canonical URI path, perhaps with an extra encoding pass
    """
    match path
    | "" => "/"
    | "/" => "/"
    else
      if path(0)? != '/' then
        // iiuc, this should never happen for a valid URL.path,
        // but after what i've seen, i don't trust the http lib
        _encoded_path("/" + path, passes)?
      else
        let segments: Array[String] = path.split("/")
        for (index, value) in segments.pairs() do
          segments(index)? = _encoded_segment(value, passes)?
        end
        "/".join(segments.values())
      end
    end

  fun _recompose_uri(uri: URL, part: URLPart, value: String): URL val ? =>
    """
    swap part of a uri using the string composition code from the URL class
    """
    var user = uri.user
    var host = uri.host
    var password = uri.password
    var path = uri.path
    var query = uri.query
    var fragment = uri.fragment

    match part
    | URLPartUser => user = value
    | URLPartPassword => password = value
    | URLPartHost => host = value
    | URLPartPath => path = value
    | URLPartQuery => query = value
    | URLPartFragment => fragment = value
    end

    // here follows the composition logic from http.URL ...

    let len =
      uri.scheme.size() + 3 + user.size() + 1 + password.size() + 1
      + host.size() + 6 + path.size() + 1 + query.size() + 1
      + fragment.size()
    let s = recover String(len) end

    if uri.scheme.size() > 0 then
      s.append(uri.scheme)
      s.append(":")
    end

    if (user.size() > 0) or (host.size() > 0) then
      s.append("//")
    end

    if user.size() > 0 then
      s.append(user)
      if password.size() > 0 then
        s.append(":")
        s.append(password)
      end
      s.append("@")
    end

    if host.size() > 0 then
      s.append(host)
      s.append(":")
      s.append(uri.port.string())
    end

    s.append(path)

    if query.size() > 0 then
      s.append("?")
      s.append(query)
    end

    if fragment.size() > 0 then
      s.append("#")
      s.append(fragment)
    end

    // now simply build() the string into a URL
    URL.build(consume s, true)?

  fun _canonical_query_string(uri: URL): String val =>
    /* TODO
     * parse/decode the keys/values into tuples,
     * sort the tuples by key, then value
     * empty values are okay
     * recompose the query string with encoded keys/values
     */
    uri.query

  fun _canonical_headers(headers: this->Array[_KV] ref): String val =>
    /* TODO
     * ensure host: or :authority (http2) exist.
     * convert header names to lowercase,
     * sort the headers by name,
     * convert multiple spaces in values to a single space,
     * trim whitespace from values,
     * join values with a comma,
     * each line is "header:value,value,value\n"
     */
    var len = headers.size()   // semi-colons and trailing newline
    for h in headers.values() do
      len = len + h.name().size() + 1
      len = len +
        match h.value()
        | None => 0
        | let s: String => s.size()
        end
    end
    let result = recover String(len) end
    for h in headers.values() do
      if result.size() != 0 then
        result.append(";")
      end
      result.append(h.name())
    end
    result.append("\n")
    result

  fun _signed_headers(headers: this->Array[_KV] ref): String val =>
    """
      join header names with a semi-colon, add a newline
    """
    var len = headers.size()   // semi-colons and trailing newline
    for h in headers.values() do
      len = len + h.name().size()
    end
    let result = recover String(len) end
    for h in headers.values() do
      if result.size() != 0 then
        result.append(";")
      end
      result.append(h.name())
    end
    result.append("\n")
    result

  fun canonical_request(): String val ? =>
    """
    compose the canonical request for signing purposes
    """
    // the important thing is to do no more than one alloc
    let result = recover String(1024) end
    result.append(_method)
    result.append("\n")
    result.append(_encoded_path(_url.path, _passes - 1)?)
    result.append("\n")
    result.append(_canonical_query_string(_url))
    result.append("\n")
    result.append(_canonical_headers(_headers))
    result.append("\n")
    result.append(_signed_headers(_headers))
    result.append("\n")
    result.append(_algo.digest(_payload))
    result

actor Main is TestList
  new create(env: Env) =>
    PonyTest(env, this)

  new make() =>
    None

  fun tag tests(test: PonyTest) =>
    test(_TestCreate)
    test(_TestHttpUrlEncoding)
    test(_TestEncodedSegment)
    //test(_TestEncodedComponents)
    test(_TestEncodedPath)
    //test(_TestEncodedQuery)
    //test(_TestEncodedHeaders)
    test(_TestSigningAlgos)
    //test(_TestCanonicalRequest)
    //test(_TestCanonicalRequestUnsigned)
    //test(_TestCredentialScope)
    //test(_TestStringToSign)
    //test(_TestDeriveKey)
    //test(_TestCalculateSignature)

class iso _TestCreate is UnitTest
  fun name(): String => "create"

  fun apply(h: TestHelper) ? =>
    let uri = "https://iam.amazonaws.com/?Action=ListUsers&Version=2010-05-08"
    let url = URL.valid(uri)?

    let headers = Map[String, String]
    headers.insert("host", url.host)
    let s = SigV4("GET", url, headers)?

class iso _TestHttpUrlEncoding is UnitTest
  fun name(): String => "encoded url"

  fun apply(h: TestHelper) ? =>
    let uri = "http://a.b.c/foo bar//../bif/"
    let url = URL.build(uri)?
    let headers = Map[String, String]
    headers.insert("host", url.host)
    let s = SigV4("GET", url, headers)?
    h.assert_eq[String](url.string(), "http://a.b.c/foo%20bar//../bif/")

class iso _TestEncodedPath is UnitTest
  fun name(): String => "encoded path"

  fun apply(h: TestHelper) ? =>
    let uri = "https://iam.amazonaws.com/?Action=ListUsers&Version=2010-05-08"
    let url = URL.valid(uri)?

    let headers = Map[String, String]
    headers.insert("host", url.host)
    let s = SigV4("GET", url, headers)?
    let func = {
      (p: String, x: String, n: U8) =>
        try
          h.assert_eq[String](s._encoded_path(p, n)?, x)
        else
          h.assert_eq[Bool](true, false)
        end
    }
    // !s3
    func("", "/", 2)
    func("/", "/", 2)
    func("//", "/", 2)
    func("!s3", "/!s3", 2)
    func("!s3 bar", "/!s3%2520bar", 2)
    func("!s3 bar//../bif baz", "/bif%2520baz", 2)
    func("!s3 bar/bif/", "/!s3%2520bar/bif/", 2)
    // s3
    func("", "/", 1)
    func("//", "//", 1)
    func("s3", "/s3", 1)
    func("s3/", "/s3/", 1)
    func("s3 bar//../bif", "/s3%20bar//../bif", 1)

class iso _TestEncodedSegment is UnitTest
  fun name(): String => "encoded segment"

  fun apply(h: TestHelper) ? =>
    let uri = "https://iam.amazonaws.com/?Action=ListUsers&Version=2010-05-08"
    let url = URL.valid(uri)?
    let headers = Map[String, String]
    headers.insert("host", url.host)
    let s = SigV4("GET", url, headers)?
    h.assert_eq[String]("", s._encoded_segment("", 0)?)
    h.assert_eq[String]("", s._encoded_segment("", 1)?)
    h.assert_eq[String]("foo", s._encoded_segment("foo", 0)?)
    h.assert_eq[String]("foo", s._encoded_segment("foo", 1)?)
    h.assert_eq[String]("foo%20bar", s._encoded_segment("foo bar", 1)?)
    h.assert_eq[String]("foo%2520bar", s._encoded_segment("foo bar", 2)?)

class iso _TestSigningAlgos is UnitTest
  fun name(): String => "signing algos"

  fun apply(h: TestHelper) =>
    let pay = "sigv4 test"
    h.assert_eq[String](Digest256.digest(pay),
      "474fff1f1f31f629b3a8932f1020ad2e73bf82e08c96d5998de39d66c8867836")
    h.assert_eq[String](Digest512.digest(pay),
      "1dee518b5b2479e9fa502c05d4726a40bade650adbc391da8f196797df0f5da62e0659ad0e5a91e185c4b047d7a2d6324fae493a0abdae7aa10b09ec8303f6fe")
    h.assert_eq[String](DigestUnsigned.digest(pay),
      "UNSIGNED-PAYLOAD")
