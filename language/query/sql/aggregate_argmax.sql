--  Input: UserId, Date
--  Output: UserId where ROW=argmax(Date), Date. (group by Date)
--  Description: for each UserId, get the row record where Date is maximized.
--  Calculate argmax(Date), for each UserId
--  Idea: for each loop logic can be implemented with JOIN in SQL, the declarative query language.
--  1. inner join after get max Date for each UserId
--  join on inequality condition
--  and aggregate with group by to maximize the column
select
Users.*
from
Users
join (
	select UserId, max([Date]) as MaxDate
	from Users
	group by UserId
) B
on Users.UserId=B.UserId and Users.[Date] = B.MaxDate


--  Inut: Users=|Date|UserId|value|...|, Activities=|Date|UserId|Event|...|. And Users.date not exactly the same as Activities.date
--  Output: Date|Event| Latest value as of Date|,
--  Description: in table Users, value changes w.r.t Date, we want find the latest value for each Date in table Activities.
--  For each Activities.Date, set Activities.Value=argmax(Users.Date).value where Users.Date <= Activities.Date.
--  Solution:
--  For each Activities.Date, find its corresponding max Users.Date, and join Users on Users.Date=max Users.Date
--  1. join on inequality condition and aggregate with group by
--  2. Join on equality condition

-- step 1: augment max Date so far from Users table for each record in Activities
select
Activities.*
, max(Users.Date) as maxDateSoFar -- argmax(Users.Date).value where Users.Date <= Activities.Date
from Activities
join Users
on Activities.UserId=Users.UserId and Activities.Date>=Users.Date
group by Users.UserId, Users.Date
;
-- step 2: Use this query as a nested subquery to join with Users table to get Users[argmax(Users.Date where Users.Date<=Activities.Date)].

select
*
from
(
	select
	Activities.UserId, Activities.Date, Activities.Event, max(Users.Date) as maxDateSoFar
	from Activities
	join Users
	on Activities.UserId=Users.UserId and Activities.Date>=Users.Date
	group by Activities.UserId, Activities.Date
) A
JOIN Users
ON A.UserId=Users.UserId and A.maxDateSoFar=Users.Date
order by A.Date desc
;

--  Alternative: below query has can be optimized since the nested query doesn't contain all information from Activities, and involes another join outside
select
*
--  Activities.Date, Users.value as latestValue, Event
from Activities
join
(
	select -- group by aggregating to maximize
	Activities.Date,
	max(Users.Date) as aDate,
	from Activities
	join Users
	on Activities.Date >= Users.Date
	group by Activities.UserId, Activities.Date
) C
on Activities.Date=C.Date
join Users on C.aDate=Users.Date -- inner join on columns maximized
order by Activities.Date desc
;
