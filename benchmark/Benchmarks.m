clear
clc
close all

%% Experimental Data
n = [ 10000,  20000,  30000,  40000,  50000,  60000,  70000,  80000,  90000,...
     100000, 200000, 300000, 400000, 500000, 600000, 700000, 800000, 900000];
m = [    15,     30,     49,     94,     89,    116,    143,    165,    192,...
        307,    544,    894,   1446,   1710,   2064,   2711,   3064,   3522];
i = [    17,     42,     71,    103,    134,    171,    207,    244,    279,...
        329,    770,   1251,   1763,   2325,   2893,   3442,   4060,   4663];
v = [    72,    169,    279,    397,    507,    638,    776,    896,   1046,...
       1187,   2701,   4376,   6074,   7959,   9783,  11894,  13860,  16206];

mean(v./m)
mean(v./i)

%% Non-linear regression
model = @(beta,x)(beta(1) + beta(2).*x.*log2(x));

m_var0 = [1.0, 1.0];
m_var = nlinfit(n, m, model, m_var0, 'ErrorModel', 'proportional');
m_var
m_fitted = model(m_var, n);

i_var0 = [1.0, 1.0];
i_var = nlinfit(n, i, model, i_var0, 'ErrorModel', 'proportional');
i_var
i_fitted = model(i_var, n);

v_var0 = [1.0, 1.0];
v_var = nlinfit(n, v, model, v_var0, 'ErrorModel', 'proportional');
v_var
v_fitted = model(v_var, n);

%% Constants
blue = [57/255, 106/255, 177/255];
orange = [218/255, 124/255, 48/255];
green = [62/255, 150/255, 81/255];
marker_size = 40;
line_width = 1.5;

%% Figure
figure
hold on
grid on

scatter(n, m, marker_size, blue, 'filled', 'o')
scatter(n, i, marker_size, orange, 'filled', '^')
scatter(n, v, marker_size, green, 'filled', 's')

plot(n, m_fitted, 'Color', blue, 'LineWidth', line_width)
plot(n, i_fitted, 'Color', orange, 'LineWidth', line_width)
plot(n, v_fitted, 'Color', green, 'LineWidth', line_width)

set(gca, 'yScale', 'log')
set(gca, 'xScale', 'log')

xlabel('Number of Points', 'FontWeight', 'bold')
ylabel('Running Time (ms)', 'FontWeight', 'bold')

legend('mutable', 'immutable', 'verified', 'Location', 'best')
