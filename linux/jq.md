# jq - command line JSON processor

## user manual

`man jq`

```text
SYNOPSIS
       jq [options...] filter [files...]

       jq can transform JSON in various ways, by selecting, iterating, reducing and otherwise mangling JSON documents. For instance, running the command jq ´map(.price) | add´ will take an array of JSON objects as input and return the sum of their "price" fields.

       jq  can accept text input as well, but by default, jq reads a stream of JSON entities (including numbers and other literals) from stdin. Whitespace is only needed to separate entities such as 1 and 2, and true and false. One or more files may be specified, in which case jq will read input from those
       instead.
```

- --slurp/-s: read the entire input stream into a large array and run the filter just once
- --raw-output/-r: output rather than JSON string with quotes.

## Idea

The idea is pipeline like functional programming.

## Usage

### Basic filters

- Identity: `.`. Output is identical to the input.
- Object identifier index: `.foo`, `.foo.bar`. When given a JSON object (aka dictionary or hash) as input, it produces the value at the key "foo", or null if there´s none present. A filter of the form `.foo.bar` is equivalent to `.foo|.bar`.
- Optional Object Identifier-Index: `.foo?`
- Array/Object Value Iterator: `.[]` reuturns all of the elements of an array.
- `.[]?`: Like `.[]`, but no errors will be output if . is not an array or object.
- Array Index: `.[2]`
- Array/String Slice: `.[10:15]`
- Comma: `,`. Fields separator
- Parenthesis `()` work as a grouping operator just as in any typical programming language.
- Pipe: `|`. The  | operator combines two filters by feeding the output(s) of the one on the left into the input of the one on the right. .a.b.c is the same as .a | .b | .c

### Types and values

- Array construction: `[]`
- Object construction: `{}`
- recursive descendent: `..`

### Builtin operators and functions

- Addition: +. For numbers, objects mering, array concatenation
- multiplication, division, modulo: *, /, %
- length: length of array, object, string
- `map(x)`, `map_values(x)`

For any filter x, map(x) will run that filter for each element of the input array, and return the outputs in a
new array. map(.+1) will increment each element of an array of numbers.

Similarly, map_values(x) will run that filter for each element, but it will return an object when an object is
passed.

`map(x)` is equivalent to `[.[] | x]`. In fact, this is how it´s defined. Similarly, `map_values(x)` is  defined  as
`.[] |= x`.

           jq ´map(.+1)´
              [1,2,3]
           => [2,3,4]

           jq ´map_values(.+1)´
              {"a": 1, "b": 2, "c": 3}
           => {"a": 2, "b": 3, "c": 4}

- del(path_expression): The builtin function del removes a key and its corresponding value from an object.

### function

List operation

- all
- any
- unique
- contains

string

- startswith
- enddwith

array

- join
- sort, sort_by(path_expression)


### regular expression

jq uses the Oniguruma regular expression library, as do php, ruby, TextMate, Sublime Text, etc, so the description here will focus on jq specifics.

	The jq regex filters are defined so that they can be used using one of these patterns:

	   STRING | FILTER( REGEX )
	   STRING | FILTER( REGEX; FLAGS )
	   STRING | FILTER( [REGEX] )
	   STRING | FILTER( [REGEX, FLAGS] )

	FLAGS is a string consisting of one of more of the supported flags:

	○   g - Global search (find all matches, not just the first)
	○   i - Case insensitive search
	○   m - Multi line mode (´.´ will match newlines)
	○   n - Ignore empty matches
	○   p - Both s and m modes are enabled
	○   s - Single line mode (´^´ -> ´\A´, ´$´ -> ´\Z´)
	○   l - Find longest possible matches
	○   x - Extended regex format (ignore whitespace and comments)


match(val), match(regex; flags)

   match outputs an object for each match it finds.

       Matches have the following fields:

       ○   offset - offset in UTF-8 codepoints from the beginning of the input
       ○   length - length in UTF-8 codepoints of the match
       ○   string - the string that it matched
       ○   captures - an array of objects representing capturing groups.

       Capturing group objects have the following fields:

       ○   offset - offset in UTF-8 codepoints from the beginning of the input
       ○   length - length in UTF-8 codepoints of this capturing group
       ○   string - the string that was captured
       ○   name - the name of the capturing group (or null if it was unnamed)

       Capturing groups that did not match anything return an offset of -1

           jq ´match(["foo", "ig"])´
              "foo bar FOO"
           => {"offset": 0, "length": 3, "string": "foo", "captures": []}, {"offset": 8, "length": 3, "string": "FOO", "captures": []}

           jq ´match("foo (?<bar123>bar)? foo"; "ig")´
              "foo bar foo foo  foo"
           => {"offset": 0, "length": 11, "string": "foo bar foo", "captures": [{"offset": 4, "length": 3, "string": "bar", "name": "bar123"}]}, {"offset": 12, "length": 8, "string": "foo  foo", "captures": [{"offset": -1, "length": 0, "string": null, "name": "bar123"}]}

           jq ´[ match("."; "g")] | length´
              "abc"
           => 3

test(val), test(regex; flags)

   Like match, but does not return match objects, only true or false for whether or not the regex matches the input.

           jq ´test("foo")´
              "foo"
           => true

           jq ´.[] | test("a b c # spaces are ignored"; "ix")´
              ["xabcd", "ABC"]
           => true, true

           jq 'map(select(.key|test("pattern";"i")))'

## Examples

    jq '[.[] | {id: .id, location: .location, vm: [.agentPoolProfiles[]|{size: .vmSize, count: .count}]}]'

### flatten an object

    jq '.key' <<EOF
    {"key": {"a": 1, "b": 2}}
    EOF

### catenate JSONs of arrays

    # flatten multiple arrays of arrays.
    jq '[.[]|.]' # output the array as it is.
    jq -s '[.[]|.[]]'  # produces an array, of which each element is the element of arrays of the array
    jq -s 'map(.[])'

### map, group by, select, sort, top slice, add sum: given an array of array

    jq 'map(.[]?) 
	| group_by(.key)
    | map({name: .[0].key, length: length, key1: .[0].key1} 
	  |select(.key1=="value1")) 
	| sort_by(-.length)
	|.[0:100]
	| map(.count)
	| add
	'

### group by and count, given an array of objects

    jq 'group_by(.key)|map({kay: .[0].key, length: length})'

### to csv

	jq -r '(map(keys) | add | unique) as $cols | map(. as $row | $cols | map($row[.])) as $rows | $cols, $rows[] | @csv'


### Regular expression

    # construct object, with regex, test
    .+{rg: (.Scope|"https://ms.portal.azure.com/#@microsoft.onmicrosoft.com/resource/subscriptions/4aaa645c-5ae2-4ae9-a17a-84b9023bc56a/resourceGroups/" +match(".*resourceGroups/(.+)/providers.*").captures[0].string)}
    # https://til.hashrocket.com/posts/uv0bjiokwk-use-jq-to-filter-objects-list-with-regex
    cat << EOF| jq '.[] | select(.id|test("a.")) | .name'
    [
      {"name": "Chris", "id": "aabbcc"},
      {"name": "Ryan", "id": "ddeeff"},
      {"name": "Ifu", "id": "aaddgg"}
    ]
    EOF

    # extract matched capture: match("...").captures[0].string, ...
    jq 'map(. + {user: .path|match(".+users/([^/]+).*"; "i").captures[0].string})' <<EOF
	[{"id": "1", "path": "host/users/a"}, {"id": "2", "path": "host/users/b/items"}]
	EOF

    [
	  {
		"id": "1",
		"path": "host/users/a",
		"user": "a"
	  },
	  {
		"id": "2",
		"path": "host/users/b/items",
		"user": "b"
	  }
	]

Reference: https://stackoverflow.com/questions/32960857/how-to-convert-arbitrary-simple-json-to-csv-using-jq

## Reference

- https://github.com/stedolan/jq/wiki/Cookbook
