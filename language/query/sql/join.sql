-- Input: two tables
-- Output: a joined table with condition
-- Idea: join is like running for each loop over two or more tables
-- Four types of JOIN
--  (INNER) JOIN: Returns records that have matching values in both tables
--  LEFT (OUTER) JOIN: Returns all records from the left table, and the matched records from the right table
--  RIGHT (OUTER) JOIN: Returns all records from the right table, and the matched records from the left table
--  FULL (OUTER) JOIN: Returns all records when there is a match in either left or right table

SELECT Orders.OrderID, Customers.CustomerName, Orders.OrderDate, Category.Category
FROM Orders
INNER JOIN (
	select *
	from Customers
	where LEN(Customers.CustomerName)>0
) A
ON Orders.CustomerID=A.CustomerID
JOIN  Category
on 1=1
and Orders.CustomerID=Category.CustomerID
where 1=1
and OrderDate is not NULL
;

