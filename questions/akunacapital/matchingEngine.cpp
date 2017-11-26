/*
 *
Write a Matching Engine
You're going to write an exchange order matching engine.

The input is from stdin, each line file has several columns separated by one space.

The first column specifies the operation to be done. Our supported operations are:

BUY
SELL
CANCEL
MODIFY
PRINT

If the first column is BUY or SELL, then this line has five columns in total:
The second column is the order type, it's either IOC or GFD.
The third column is the price you want to buy or sell, it's an integer.
The fourth column shows the quantity of that buy or sell, it's an integer. Both the price and quantity are positive numbers.
The fifth column is the order id, it can be arbitrary words.

If the first column is CANCEL, then this line has two columns in total:
The second column is the order id, it means that order needs to be deleted, it can't be traded anymore.
If that order id doesn't exist, just do nothing.

If the first column is MODIFY, then this line has five columns in total:
The second column is the order id, it means that order needs to be modified.
The third column is either BUY or SELL.
The fourth column is the new price of that order.
The fifth column is the new quantity of that order.

If that order id doesn't exist, just do nothing.

(Note: that we can't modify an IOC order type, as we'll mention later.)
MODIFY is a powerful operation, e.g. a BUY order can be modified to a SELL order.
BUY GFD 1000 10 order1
MODIFY order1 SELL 1000 10

If the first column is PRINT, then there'll be no following columns in this line. You're supposed to output the current price book according to our formats.

Output format:
SELL:
price1 qty1
price2 qty2
BUY:
price1 qty1
price2 qty2

The price for SELL section must be decreasing and corresponding the price for BUY section must be decreasing.

Now let's talk the order type:
The GFD order (stands for "good for day") will stay in the order book until it's been all traded.
the IOC order (stands for "insert or cancel") means if it can't be traded immediately, it will be cancelled right away. If it's only partially traded, the non-traded part is cancelled.

The rule for matching is simple, if there's a price cross meaning someone is willing to buy at a price higher than or equal with the current selling price, these two orders are traded.
And you're also supposed to print out the traded information when one order is traded.

For example:
BUY GFD 1000 10 order1
SELL GFD 900 10 order2
After you process the second line, we know that these two orders can be traded, so you need to output:
TRADE order1 1000 10 order2 900 10

(NOTE: The "TRADE order1 price1 qty1 order2 price2 qty2" message should be output whenever there's a trade from the matching engine, every trade must has this output, it doesn't rely on the "PRINT" operation.)
Basically it shows two orders' information, order id followed by its price and its traded quantity. (Real matching engine will have only one traded price, but to make things simple, we output two prices by each.) The sequence for order1 and order2 is decided by who sends the order first.

For example:
SELL GFD 900 10 order2
BUY GFD 1000 10 order1
Then the output is:
TRADE order2 900 10 order1 1000 10

One principle rule for a matching engine is to be FAIR, it means who sends the order first gets traded first if it meets the criteria.

For example:
BUY GFD 1000 10 order1
BUY GFD 1000 10 order2
SELL GFD 900 20 order3

The output will be:
TRADE order1 1000 10 order3 900 10
TRADE order2 1000 10 order3 900 10

There's another interesting thing for MODIFY operation, "MODIFY" will lose its original place. So
BUY GFD 1000 10 order1
BUY GFD 1000 10 order2
MODIFY order1 BUY 1000 20
SELL GFD 900 20 order3

Because order1 is modified in the middle, now order2 is in the first place, order1 is in the second place, so the output will be:

TRADE order2 1000 10 order3 900 10
TRADE order1 1000 10 order3 900 10

We guarantee that:
order id is unique.

Example 1:
BUY GFD 1000 10 order1
PRINT

The output of above would be:
SELL:
BUY:
1000 10

Example 2:
BUY GFD 1000 10 order1
BUY GFD 1000 20 order2
PRINT

The output of above would be:
SELL:
BUY:
1000 30

Example 3:
BUY GFD 1000 10 order1
BUY GFD 1001 20 order2
PRINT

The output of above would be:
SELL:
BUY:
1001 20
1000 10

Example 4:
BUY GFD 1000 10 order1
SELL GFD 900 20 order2
PRINT

The output of above would be:
TRADE order1 1000 10 order2 900 10
SELL:
900 10
BUY:

Any input with price <= 0 or quantity <= 0 or empty order id is invalid. Should be ignored by the application.
*/

#include <map>
#include <set>
#include <list>
#include <cmath>
#include <ctime>
#include <deque>
#include <queue>
#include <stack>
#include <string>
#include <bitset>
#include <cstdio>
#include <limits>
#include <vector>
#include <climits>
#include <cstring>
#include <cstdlib>
#include <fstream>
#include <numeric>
#include <sstream>
#include <iostream>
#include <algorithm>
#include <unordered_map>
#include <memory>



#define TEST false

void test();

using namespace std;

const string BUY    = "BUY";
const string SELL   = "SELL";
const string CANCEL = "CANCEL";
const string MODIFY = "MODIFY";
const string PRINT  = "PRINT";

const string IOC = "IOC";
const string GFD = "GFD";

typedef tuple<int, int> OrderKey;
struct Order {
    string operation; // buy, sell, cancel, modify, print
    string type; // order type: IOC, GFD
    int price;
    int quantity;
    string id; // order id: order1, order2
    string operation1; // modified operation
    int timestamp;

    Order(): timestamp(clock()) {}

    static shared_ptr<Order> parseOrder(string line) {
        istringstream iss(line);
        shared_ptr<Order> order = make_shared<Order>();
        order->timestamp = clock();

        iss >> order->operation;
        bool valid = true;
        if (order->operation == BUY) {
            order->operation = BUY;
            valid = order->parseBuy(iss);
        } else if (order->operation == SELL) {
            valid = order->parseSell(iss);
        } else if (order->operation == CANCEL) {
            valid = order->parseCancel(iss);
        } else if (order->operation == MODIFY) {
            valid = order->parseModify(iss);
        } else if (order->operation == PRINT) {
            // ORDER
            valid = order->parsePrint(iss);
        } else valid = false;
        //if (!valid) {
            //cerr << "INVALID INPUT! " << line << " " << order->price << " id:" << order->id << endl;
        //}
        return valid ? order: NULL;
    }

    tuple<int, int> getKey() {
        return make_tuple(price, timestamp);
    }

    bool parseBuy(istringstream& iss) {
        iss >> type >> price >> quantity >> id;
        return (type == IOC || type == GFD) && price > 0 && quantity > 0 && !id.empty();
    }

    bool parseSell(istringstream& iss) {
        return parseBuy(iss);
    }

    bool parseCancel(istringstream& iss) {
        iss >> id;
        return !id.empty();
    }

    bool parseModify(istringstream& iss) {
        iss >> id >> operation1 >> price >> quantity;
        return price > 0 && quantity > 0 && !id.empty();
    }

    bool parsePrint(istringstream& iss) {
        return true;
    }
};

// FIXME: more than half cases are failed, even segmentation fault.
class Engine {
    public:
        //Engine() {};
        map<OrderKey, shared_ptr<Order>> orders_buy;
        map<OrderKey, shared_ptr<Order>> orders_sell;
        map<string, OrderKey> id2key_buy; // hash table, mapping from order id to index
        map<string, OrderKey> id2key_sell;

        void process(string line) {

            shared_ptr<Order>order = Order::parseOrder(line);
            if (!order)  return;

            if (order->operation == BUY) {
                trade(order);
            } else if (order->operation == SELL) {
                trade(order);
            } else if (order->operation == CANCEL) {
                cancel(order);
            } else if (order->operation == MODIFY) {
                // modify and trade?
                shared_ptr<Order> oldOrder = modifyOrder(order);
                trade(oldOrder);
            } else if (order->operation == PRINT) {
                // ORDER
                print();
            };
        };

        void addOrder(shared_ptr<Order> order) {
            if (order->operation == BUY) {
                orders_buy.insert(make_pair(order->getKey(), order));
                this->id2key_buy[order->id] = order->getKey();
            } else if (order->operation == SELL) {
                orders_sell.insert(make_pair(order->getKey(), order));
                this->id2key_sell[order->id] = order->getKey();
            }
        }

        void addBuyer(shared_ptr<Order> order) {
            orders_buy.insert(make_pair(order->getKey(), order));
            this->id2key_buy[order->id] = order->getKey();
        }

        void addSeller(shared_ptr<Order> order) {
            orders_sell.insert(make_pair(order->getKey(), order));
            this->id2key_sell[order->id] = order->getKey();
        }

        void cancel(shared_ptr<Order> order) {
            OrderKey key;
            shared_ptr<Order> oldOrder;
            if (id2key_buy.find(order->id) != id2key_buy.end()) {
                key = this->id2key_buy[order->id];
                orders_buy.erase(key);
                id2key_buy.erase(order->id);
            } else if (id2key_sell.find(order->id) != id2key_sell.end()) {
                key = this->id2key_sell[order->id];
                orders_sell.erase(key);
                id2key_sell.erase(order->id);
            }
        }

        map<int, int> _getPriceCount(map<OrderKey, shared_ptr<Order>> orders) {

            map<int, int> priceCount;
            accumulate(orders.begin(), orders.end(), 0,
                    [&priceCount,this](int res, map<OrderKey, shared_ptr<Order>>::value_type v) {
                        priceCount[v.second->price] += v.second->quantity;
                        return 0;
                    });
            return priceCount;
        }

        void print() {
            map<int, int> priceCount;
            priceCount = _getPriceCount(orders_sell);
            cout << "SELL:" << endl;
            accumulate(priceCount.begin(), priceCount.end(), 0,[](int, map<int, int>::value_type v){
                        cout << v.first << " " << v.second << endl;
                        return 0;
                    });
            //priceCount.clear();
            priceCount = _getPriceCount(orders_buy);
            cout << "BUY:" << endl;
            accumulate(priceCount.rbegin(), priceCount.rend(), 0,[](int, map<int, int>::value_type v){
                        cout << v.first << " " << v.second << endl;
                        return 0;
                    });
        }

        shared_ptr<Order> modifyOrder(shared_ptr<Order> order) {
            OrderKey key;
            shared_ptr<Order> oldOrder = NULL;
            map<OrderKey, shared_ptr<Order>> *orders = NULL;

            if (id2key_buy.find(order->id) != id2key_buy.end()) {
                key = this->id2key_buy[order->id];
                orders = &orders_buy;
            } else if (id2key_sell.find(order->id) != id2key_sell.end()) {
                key = this->id2key_sell[order->id];
                orders = &orders_sell;
            } else {
                return NULL;
            }
            if (orders->find(key) != orders->end()) {
                oldOrder = orders->at(key);
                orders->erase(key);
            }
            if (!oldOrder) {
                return NULL;
            }
            oldOrder->operation = order->operation1;
            oldOrder->price = order->price;
            oldOrder->quantity = order->quantity;
            oldOrder->timestamp = clock();
            return oldOrder;
        }

        bool trade(shared_ptr<Order> order) {
            if (!order)  return false;
            map<int, shared_ptr<Order>> others; // orders possible to trade with

            int quantity = order->quantity;
            if (order->operation == BUY) {
                map<OrderKey, shared_ptr<Order>>::iterator seller_it = matchSeller(order);
                map<OrderKey, shared_ptr<Order>>::reverse_iterator itr(seller_it);
                for (auto it = itr; it != orders_sell.rend(); ++it) {
                    others.insert(make_pair(it->second->timestamp, it->second));
                }
                // else, it's discarded anyway
            } else if (order->operation == SELL) {
                map<OrderKey, shared_ptr<Order>>::iterator buyer_it = matchBuyer(order);
                for (auto it = buyer_it; it != orders_buy.end(); ++it) {
                    others.insert(make_pair(it->second->timestamp, it->second));
                }
            }
            for (auto it = others.begin(); quantity > 0 && it != others.end(); ++it) {
                shared_ptr<Order> other = it->second;
                int quantity_traded = min(quantity, it->second->quantity);
                cout << "TRADE "
                    << other->id << " " << other->price << " " << quantity_traded << " "
                    << order->id << " " << order->price << " " << quantity_traded
                    << endl;
                quantity -= quantity_traded;
                other->quantity -= quantity_traded;
                if (other->quantity <= 0) {
                    //orders_buy.erase(other->getKey());
                    cancel(other);
                }
            }
            order->quantity = quantity;
            // deal with remaining quantity
            if (quantity > 0 && order->type == GFD) {
                addOrder(order);
            }
            return false;
        }

        map<OrderKey, shared_ptr<Order>>::iterator matchBuyer(shared_ptr<Order> order) {
            return orders_buy.lower_bound(order->getKey());
        }

        map<OrderKey, shared_ptr<Order>>::iterator matchSeller(shared_ptr<Order> order) {
            return orders_sell.upper_bound(order->getKey());
        }
};

shared_ptr<Engine> engine = make_shared<Engine>();

int main(int argc, char **argv) {
    /* Enter your code here. Read input from STDIN. Print output to STDOUT */

    string line;
    while(getline(cin, line)) {
        if (line.empty()) { continue; }
        engine->process(line);
    }
}


void test() {
    string input;

    input = "";

    input = "BUY GFD 1000 10 order1"
        "PRINT"
    ;

    //cout << input;

}
