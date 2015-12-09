from __future__ import division
import numpy as np
from random import randint
import copy
from matplotlib import mpl,pyplot
import matplotlib.pyplot as plt
import random
import itertools

def initiate_CA_random(n):
	'''input: n where n x n is the size of the board
	   output: a 2D CA board with n x n many cells 
	           initiated randomly
	           and 0 = rock, 1 = paper, 2 = scissors, 3 = empty
	'''
	return np.random.random_integers(0,3,(n,n))

def det_local_neighborhood(cell_index,board):
	'''input: cell index, the CA board
	   output: the local neighborhood values of the given cell index 
	   note: wraparound occurs
	'''
	i = cell_index[0]
	j = cell_index[1]
	n = board.shape[0]

	neighborhood_indices = []
	neighborhood_values = []

	neighborhood_indices = [(i,j+1),(i,j-1),(i+1,j+1),(i+1,j),(i+1,j-1),(i-1,j+1),(i-1,j),(i-1,j-1)]
	for index in neighborhood_indices:
		neighborhood_values.append(board[index[0] % n][index[1] % n])
	return neighborhood_values

def det_global_neighborhood(cell_index,board):
	'''input: cell index, the CA board
	   output: the global neighborhood values of the given cell index 
	   note: wraparound occurs
	'''
	i = cell_index[0]
	j = cell_index[1]
	n = board.shape[0]

	neighborhood_values = []
	for l in range(n):
		for m in range(n):
			if (l,m) != (i,j): #so as to remove the focal point
				neighborhood_values.append(board[l][m])
	return neighborhood_values

def det_new_cell_value(cell_index,board,neighborhood_method,delta_r,delta_p,delta_s0,T):
	'''input: the index of the cell, the CA board, the neighborhood desired,
	          probability of death for R cell, P cell, S cell without R neighbors, toxicity
	   output: the value the cell at cell_index should take after 1 time step
	'''
	i = cell_index[0]
	j = cell_index[1]
	n = board.shape[0]
	neighborhood_values = []

	#determine neighborhood values of cell to update

	if neighborhood_method == "local":
		neighborhood_values = det_local_neighborhood(cell_index,board)

	if neighborhood_method == "global":
		neighborhood_values = det_global_neighborhood(cell_index,board)


	#neighborhood is now determined
	#now for updating the cell value

	if board[i][j] == 3: # if cell to update is empty
		r_count = neighborhood_values.count(0)
		p_count = neighborhood_values.count(1)
		s_count = neighborhood_values.count(2)
		e_count = neighborhood_values.count(3)
		N = len(neighborhood_values)
		r_prob = r_count/N #f_r
		p_prob = p_count/N #f_p
		s_prob = s_count/N #f_s
		e_prob = e_count/N #f_e
		#note: blue = 0 = rock, black = 1 = paper, red = 2 = scissors

		pvals = [r_prob,p_prob,s_prob,e_prob]
		filler_cell = np.where(np.random.multinomial(1,pvals))[0][0]

		return filler_cell
		
	else: #if cell to update is not empty
		if board[i][j] == 0: #cell is rock
			roll = random.random()
			if roll < delta_r: #rock cell is killed so now empty cell
				return 3 
			else: #no death. stay the same
				return 0
		if board[i][j] == 1: #cell is paper
			roll = random.random()
			if roll < delta_p: #paper cell is killed so now empty cell 
				return 3 
			else:
				return 1 #no death. stay the same
		if board[i][j] == 2: #cell is scissors
			roll = random.random()
			r_count = neighborhood_values.count(0)
			N = len(neighborhood_values)
			delta_s = delta_s0 + T*(r_count/N) #delta_s is not fixed
			if roll < delta_s: #scissors cell is killed so now empty cell 
				return 3 
			else: #no death. stay the same
				return 2 

def update_board_once(board,neighborhood_method,delta_r,delta_p,delta_s0,T):
	'''input: the CA board, the neighborhood method,probability of death for R cell, P cell, S cell without R neighbors, toxicity
	   output: the CA board after 1 timestep, the number of rock cells, paper cells, and scissors cells
	'''
	n = board.shape[0]
	old_board = copy.deepcopy(board)

	for i in range(0,n*n): #according to kerr: every unit of time is an epoch (n^2)
		#randomly choose a cell to update
		xupdate = randint(0,n-1)
		yupdate = randint(0,n-1)

		#update cell xupdate,yupdate in board
		board[xupdate][yupdate] = det_new_cell_value((xupdate,yupdate),board,neighborhood_method,delta_r,delta_p,delta_s0,T)

	#also need to return the number of r,p,s
	r_count = count_cell(board,0)
	p_count = count_cell(board,1)
	s_count = count_cell(board,2)
	return board,r_count,p_count,s_count

def count_cell(board,value):
	'''input: the board, the value to count (0=rock,1=paper,2=scissors,3=empty)
	   output: number of occurrences of the value in the board
	'''
	count = 0
	n = board.shape[0]
	for i in range(0,n):
		for j in range(0,n):
			if board[i][j] == value:
				count = count + 1
	return count

def update_board(board,neighborhood_method,time_steps,delta_r,delta_p,delta_s0,T):
	'''input: the CA board, the neighborhood desired, the number of time steps,
	          probability of death for R cell, P cell, S cell without R neighbors, toxicity
	   output: the CA board after the designated number of timesteps, the frequencies of each cell value after every time step
	'''
	r_counts = [count_cell(board,0)]
	p_counts = [count_cell(board,1)]
	s_counts = [count_cell(board,2)]
	old_board = board
	for i in range(time_steps):
		#color_board(old_board) #uncomment if you wish to see the board at each time step
		#print "time step: ",i
		new_board,r,p,s = update_board_once(old_board,neighborhood_method,delta_r,delta_p,delta_s0,T)
		old_board = new_board
		r_counts.append(r)
		p_counts.append(p)
		s_counts.append(s)
	return new_board,r_counts,p_counts,s_counts

def make_abundance_plot(time_steps,r_counts,p_counts,s_counts):
	'''input: the number of time steps, the frequencies of each cell value at every time step
	   output: NA but prints the abundance plots
	   note: blue = 0 = rock, black = 1 = paper, red = 2 = scissors
	'''
	timesteps = [i for i in range(0,time_steps+1)]
	plt.xlabel(r'$time steps$')
	plt.ylabel(r'$abundance$')
	
	#plt.ylim([0,5])
	#fig1 = plt.plot(timesteps,np.log10(r_counts),'b-',label = r'$rock$')
	#fig2 = plt.plot(timesteps,np.log10(p_counts),'k-',label = r'$paper$')
	#fig3 = plt.plot(timesteps,np.log10(s_counts),'r-',label = r'$scissors$')

	#plt.ylim([0,200])
	fig1 = plt.plot(timesteps,r_counts,'b-',label = r'$rock$')
	fig2 = plt.plot(timesteps,p_counts,'k-',label = r'$paper$')
	fig3 = plt.plot(timesteps,s_counts,'r-',label = r'$scissors$')

	plt.legend(loc = 0)
	plt.show()


def color_board(board,ms):
	'''input: a CA board, marker size
	   output: N/A but prints out the CA board colored in the following fashion
	            blue = 0 = rock, black = 1 = paper, red = 2 = scissors, white = 3 = empty
	'''
	
	n = board.shape[0]
	rockCellsX = []
	rockCellsY = []
	paperCellsX = []
	paperCellsY = []
	scissorsCellsX = []
	scissorsCellsY = []
	emptyCellsX = []
	emptyCellsY = []

	for i in range(0,n):
		for j in range(0,n):
			if board[i][j] == 0: #rock
				rockCellsX.append(i)
				rockCellsY.append(j)
			if board[i][j] == 1: #paper
				paperCellsX.append(i)
				paperCellsY.append(j)
			if board[i][j] == 2: #scissors
				scissorsCellsX.append(i)
				scissorsCellsY.append(j)
			if board[i][j] == 3: #empty
				emptyCellsX.append(i)
				emptyCellsY.append(j)

	plt.xlim([-.5,n-.5])
	plt.ylim([-.5,n-.5])
	if rockCellsX: #if not empty 
		fig1 = plt.plot(rockCellsX,rockCellsY,'b.',label = r'$rock$',marker = 's',markersize = ms)
	if paperCellsX:
		fig2 = plt.plot(paperCellsX,paperCellsY,'k.',label = r'$paper$',marker = 's',markersize = ms)
	if scissorsCellsX:
		fig3 = plt.plot(scissorsCellsX,scissorsCellsY,'r.',label = r'$scissors$',marker = 's',markersize = ms)
	if emptyCellsX:
		fig4 = plt.plot(emptyCellsX,emptyCellsY,'w.',label = r'$empty$',marker = 's',markersize = ms)
	#plt.legend(loc = 0)
	pyplot.axis('off')
	plt.show()

def coexistence(neighborhood_method):
	'''input: the neighborhood method
	   output: the parameter combos, coexistence probabilities 
	'''
	n = 100
	time_steps = 1000
	delta_r = 1/3
	delta_s0 = 1/4
	numRuns = 10 

	Ts = [.35,.45,.55,.65,.75] 
	delta_ps = [.325,.3125,.3,.2875,.275] 

	pairParams = []
	for y in delta_ps:
		for x in Ts:
			pairParams.append((x,y))

	#fill in matrix
	coexistenceProbs = []
	coexistenceProbsrow = [] 
	for pairParam in pairParams: 
		T = pairParam[0]
		delta_p = pairParam[1]
		print "T,delta_p: ",(T,delta_p)
		coexistence = 0
		for i in range(0,numRuns): #number of simulated runs per pairParam
			initial_board = initiate_CA_random(n)
			new_board,r,p,s = update_board(initial_board,neighborhood_method,time_steps,delta_r,delta_p,delta_s0,T)
			if r[-1]>0 and p[-1]>0 and s[-1]> 0: #coexistence does occur
				coexistence = coexistence + 1
		coexistenceProb = coexistence/numRuns
		print "coexistence prob: ",coexistenceProb
		coexistenceProbs.append(coexistenceProb)
	return pairParams,coexistenceProbs

def main():

	#things should die: less diversity
	n = 20 #kerr uses 250
	ms = 20 # for kerr: use 2
	time_steps = 100 #kerr uses 500
	neighborhood_method = "global"

	#things should live: more diversity
	#n = 20 #kerr uses 250
	#ms = 20 #for kerr: use 2
	#time_steps = 100 #kerr uses 5000
	#neighborhood_method = "local"
	
	#kerr uses these params
	#initial_board = initiate_CA_random(n)
	#delta_r = 1/3
	#delta_s0 = 1/4
	#delta_p = 10/32
	#T = 3/4

	#color_board(initial_board,ms)	
	#new_board,r,p,s = update_board(initial_board,neighborhood_method,time_steps,delta_r,delta_p,delta_s0,T)
	#color_board(new_board,ms)
	#make_abundance_plot(time_steps,r,p,s)


main()

