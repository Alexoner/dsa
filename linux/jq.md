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
- Optional Object Identifier-Index: `.foo?`
- Array/Object Value Iterator: `.[]`
- Array Index: .[2]
- Array/String Slice: .[10:15]
- Comma: ,. Fields separator
- Pipe: |. The  | operator combines two filters by feeding the output(s) of the one on the left into the input of the one on the right. .a.b.c is the same as .a | .b | .c
- Parenthesis
  Parenthesis work as a grouping operator just as in any typical programming language.

### Types and values

- Array construction: `[]`
- Object construction: `{}`
- recursive descendent: `..`

### Builtin operators and functions

- Addition: +. For numbers, objects mering, array concatenation
- multiplication, division, modulo: *, /, %
- length: length of array, object, string
- map(x), map_values(x)

       For any filter x, map(x) will run that filter for each element of the input array, and return the outputs in a
       new array. map(.+1) will increment each element of an array of numbers.

       Similarly, map_values(x) will run that filter for each element, but it will return an object when an object is
       passed.

       map(x) is equivalent to [.[] | x]. In fact, this is how it´s defined. Similarly, map_values(x) is  defined  as
       .[] |= x.

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

TODO

## Examples

    # flatten multiple arrays of arrays.
    jq -s '[.[]|.[]]'
    jq -s 'map(.[])'

    jq '[.[] | {id: .id, location: .location, vm: [.agentPoolProfiles[]|{size: .vmSize, count: .count}]}]'

### to csv

Reference: https://stackoverflow.com/questions/32960857/how-to-convert-arbitrary-simple-json-to-csv-using-jq

	jq -r '(map(keys) | add | unique) as $cols | map(. as $row | $cols | map($row[.])) as $rows | $cols, $rows[] | @csv'

## Reference

- https://github.com/stedolan/jq/wiki/Cookbook
