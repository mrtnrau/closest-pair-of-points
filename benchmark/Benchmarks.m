clear
clc
close all

%% Experimental Data
n = [ 10000,  20000,  30000,  40000,  50000,  60000,  70000,  80000,  90000,...
     100000, 200000, 300000, 400000, 500000, 600000, 700000, 800000, 900000];
m = [    44,     87,    118,    166,    166,    196,    235,    270,    299,...
        340,    818,   1381,   1369,   2493,   2315,   3208,   3758,   4317];
i = [    40,     95,    161,    225,    290,    362,    440,    515,    594,...
        673,   1589,   2568,   3603,   4700,   5847,   6970,   8127,   9368];
v = [   187,    432,    693,    970,   1237,   1543,   1858,   2176,   2482,...
       2794,   6213,   9962,  13655,  17734,  21857,  25820,  30207,  34696];

mean(v./m)
mean(v./i)

%% Non-linear regression
model = @(beta,x)(beta(1).*x.*log2(x));

m_var0 = 0.0002;
m_var = nlinfit(n, m, model, m_var0, 'ErrorModel', 'proportional');
m_var
m_fitted = model(m_var, n);

i_var0 = 0.0005;
i_var = nlinfit(n, i, model, i_var0, 'ErrorModel', 'proportional');
i_var
i_fitted = model(i_var, n);

v_var0 = 0.002;
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
ylabel('Execution Time (ms)', 'FontWeight', 'bold')

legend('mutable', 'immutable', 'verified', 'Location', 'best')
