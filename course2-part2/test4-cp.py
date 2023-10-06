# supports departure time and custom grace times

staying_time = [3, 3, 5]
# 3 means 1 grace time before, 1 grace time after, 1 period
# staying_time = departure_time - arrival_time + 1 (or +2)
# sum(X[a][b][c]==staying_time[a])