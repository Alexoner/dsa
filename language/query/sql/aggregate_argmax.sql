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


--  Inut: a=|Date|value|, b=|Date|Activity|. And a.date not exactly the same as b.date
--  Output: Date|Activity| Latest value as of Date|,
--  Description: in table a, value changes w.r.t Date, we want find the latest value for each Date in table b.
--  For each b.Date, set b.Value=argmax(a.Date).value where a.Date <= b.Date.
--  Solution:
--  For each b.Date, find its corresponding max a.Date, and join a on a.Date=max a.Date
--  1. join on inequality condition and aggregate with group by
--  2. Join on equality condition

select
b.date, a.value as latestValue, activity
from (
	select -- group by aggregating to maximize
		b.date,
		max(a.date) as aDate, -- argmax(a.date).value where a.date <= b.date
		Activity as latestValue
	from b
	join a
	on b.date >= a.date
	group by b.date
) c
join a on c.aDate=a.date -- inner join on columns maximized
order by b.date desc
;
