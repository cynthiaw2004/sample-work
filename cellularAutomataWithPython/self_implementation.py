import numpy as np
from random import randint
import copy
from matplotlib import mpl,pyplot
import matplotlib.pyplot as plt
import random

def game(x,y):
	'''input: two players' actions
	          0 = rock, 1 = paper, 2 = scissors
	   output: winning action
	'''
	if x == y:
		return x
	actions = set([x,y])
	if actions == set([0,1]):
		return 1
	if actions == set([1,2]):
		return 2
	if actions == set([0,2]):
		return 0

def initiate_CA_random(n):
	'''input: n where n x n is the size of the board
	   output: a 2D CA board with n x n many cells 
	           initiated randomly
	           and 0 = rock, 1 = paper, 2 = scissors
	'''
	return np.random.random_integers(0,2,(n,n))

def initiate_CA_sector(n):
	'''input: n where n x n is the size of the board
	          n must be divisible by 3
	   output: a 2D CA board with n x n many cells 
	           initiated by sectors
	           and 0 = rock, 1 = paper, 2 = scissors
	'''
	board = np.zeros((n,n))
	derp = np.split(board,3)
	derp[1].fill(1)
	derp[2].fill(2)
	return board

def det_moore_neighborhood(cell_index,board,radius):
	'''input: cell index, the CA board, the radius of the neighborhood_indices
	   output: the moore neighborhood values of the given cell index with given radius
	   note: wraparound occurs
	'''
	i = cell_index[0]
	j = cell_index[1]
	n = board.shape[0]

	neighborhood_indices = []
	neighborhood_values = []

	if radius == 1:
		neighborhood_indices = [(i,j+1),(i,j-1),(i+1,j+1),(i+1,j),(i+1,j-1),(i-1,j+1),(i-1,j),(i-1,j-1)]
		for index in neighborhood_indices:
			neighborhood_values.append(board[index[0] % n][index[1] % n])
		return neighborhood_values

	if radius == 2:
		neighborhood_indices = [(i,j+1),(i,j-1),(i+1,j+1),(i+1,j),(i+1,j-1),(i-1,j+1),(i-1,j),(i-1,j-1),(i-2,j+2),(i-1,j+2),(i,j+2),(i+1,j+2),(i+2,j+2),(i-2,j-2),(i-1,j-2),(i,j-2),(i+1,j-2),(i+2,j-2),(i-2,j+1),(i+2,j+1),(i-2,j),(i+2,j),(i-2,j-1),(i+2,j-1)]
		for index in neighborhood_indices:
			neighborhood_values.append(board[index[0] % n][index[1] % n])
		return neighborhood_values

def det_von_neumann_neighborhood(cell_index,board,radius):
	'''input: cell index, the CA board, the radius of the neighborhood_indices
	   output: the von neumann neighborhood values of the given cell index with given radius
	   note: wraparound occurs
	'''	
	i = cell_index[0]
	j = cell_index[1]
	n = board.shape[0]

	neighborhood_indices = []
	neighborhood_values = []

	if radius == 1:
		neighborhood_indices = [(i,j+1),(i,j-1),(i+1,j),(i-1,j)]
		for index in neighborhood_indices:
			neighborhood_values.append(board[index[0] % n][index[1] % n])
		return neighborhood_values

	if radius == 2:
		neighborhood_indices = [(i,j+1),(i,j-1),(i+1,j+1),(i+1,j),(i+1,j-1),(i-1,j+1),(i-1,j),(i-1,j-1),(i,j+2),(i,j-2),(i-2,j),(i+2,j)]
		for index in neighborhood_indices:
			neighborhood_values.append(board[index[0] % n][index[1] % n])
		return neighborhood_values

def det_new_cell_value(cell_index,board,neighborhood_method,radius,update_method):
	'''input: the index of the cell, the CA board, the neighborhood desired and its radius, the update method
	   output: the value the cell at cell_index should take after 1 time step
	'''
	i = cell_index[0]
	j = cell_index[1]
	n = board.shape[0]
	neighborhood_values = []

	if neighborhood_method == "moore":
		neighborhood_values = det_moore_neighborhood(cell_index,board,radius)

	if neighborhood_method == "neumann":
		neighborhood_values = det_von_neumann_neighborhood(cell_index,board,radius)

	#neighborhood is now determined
	#now for update

	if update_method == "random":
		neighbor_value_to_fight = random.choice(neighborhood_values)
		return game(neighbor_value_to_fight,board[i][j])

	if update_method == "all":
		for neighbor_value in neighborhood_values:
			#print "cell: ", board[i][j]
			#print "neighbor: ",neighbor_value
			if game(neighbor_value,board[i][j]) != board[i][j]: #current cell is beaten by a neighbor
				return game(neighbor_value,board[i][j]) 
		return board[i][j]

def color_board(board,ms):
	'''input: a CA board,marker size
	   output: N/A but prints out the CA board colored in the following fashion
	            blue = 0 = rock, black = 1 = paper, red = 2 = scissors
	'''
	
	n = board.shape[0]
	rockCellsX = []
	rockCellsY = []
	paperCellsX = []
	paperCellsY = []
	scissorsCellsX = []
	scissorsCellsY = []

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


	plt.xlim([-.5,n-.5])
	plt.ylim([-.5,n-.5])
	if rockCellsX: #if not empty 
		fig1 = plt.plot(rockCellsX,rockCellsY,'b.',label = r'$rock$',marker = 's',markersize = ms)
	if paperCellsX:
		fig2 = plt.plot(paperCellsX,paperCellsY,'k.',label = r'$paper$',marker = 's',markersize = ms)
	if scissorsCellsX:
		fig3 = plt.plot(scissorsCellsX,scissorsCellsY,'r.',label = r'$scissors$',marker = 's',markersize = ms)
	#plt.legend(loc = 0)
	pyplot.axis('off')
	plt.show()

def update_board_once(board,neighborhood_method,radius,update_method):
	'''input: the CA board, the neighborhood desired and its radius, the update method
	   output: the CA board after 1 timestep, the number of rock cells, paper cells, and scissors cells
	'''
	n = board.shape[0]
	old_board = copy.deepcopy(board)
	for i in range(0,n):
		for j in range(0,n):
			#update cell i,j in board
			board[i][j] = det_new_cell_value((i,j),old_board,neighborhood_method,radius,update_method)
	#also need to return the number of r,p,s
	r_count = count_cell(board,0)
	p_count = count_cell(board,1)
	s_count = count_cell(board,2)
	return board,r_count,p_count,s_count

def count_cell(board,value):
	'''input: the board, the value to count (0=rock,1=paper,2=scissors)
	   output: number of occurrences of the value in the board
	'''
	count = 0
	n = board.shape[0]
	for i in range(0,n):
		for j in range(0,n):
			if board[i][j] == value:
				count = count + 1
	return count


def update_board(board,neighborhood_method,radius,update_method,time_steps):
	'''input: the CA board, the neighborhood desired and its radius, the update method, the number of time steps
	   output: the CAT board after the designated number of timesteps, the frequencies of each cell value after every time step
	'''
	r_counts = [count_cell(board,0)]
	p_counts = [count_cell(board,1)]
	s_counts = [count_cell(board,2)]
	old_board = board
	for i in range(time_steps):
		print "time step: ",i
		#color_board(old_board) #uncomment if you wish to see the board at each time step
		new_board,r,p,s = update_board_once(old_board,neighborhood_method,radius,update_method)
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

	#
	#plt.xlim([])
	plt.xlabel(r'$time steps$')
	plt.ylabel(r'$abundance$')
	fig1 = plt.plot(timesteps,r_counts,'b-',label = r'$rock$')
	fig2 = plt.plot(timesteps,p_counts,'k-',label = r'$paper$')
	fig3 = plt.plot(timesteps,s_counts,'r-',label = r'$scissors$')
	plt.legend(loc = 4)
	plt.show()


def main():
	n = 21
	ms = 20
	time_steps = 500

	#param to try:

	##randomI,moore,1,all
	#initial_board = initiate_CA_random(n)
	#neighborhood_method = "moore"
	#radius = 1
	#update_method = "all"

	##randomI,moore,1,random
	#initial_board = initiate_CA_random(n)
	#neighborhood_method = "moore"
	#radius = 1
	#update_method = "random"
	
	##randomI,moore,2,all
	#initial_board = initiate_CA_random(n)
	#neighborhood_method = "moore"
	#radius = 2
	#update_method = "all"

	##randomI,moore,2,random
	#initial_board = initiate_CA_random(n)
	#neighborhood_method = "moore"
	#radius = 2
	#update_method = "random"

	###

	##randomI,neumann,1,all
	#initial_board = initiate_CA_random(n)
	#neighborhood_method = "neumann"
	#radius = 1
	#update_method = "all"

	##randomI,neumann,1,random
	#initial_board = initiate_CA_random(n)
	#neighborhood_method = "neumann"
	#radius = 1
	#update_method = "random"

	##randomI,neumann,2,random
	#initial_board = initiate_CA_random(n)
	#neighborhood_method = "neumann"
	#radius = 2
	#update_method = "random"

	##randomI,neumann,2,all
	#initial_board = initiate_CA_random(n)
	#neighborhood_method = "neumann"
	#radius = 2
	#update_method = "all"

	###

	##sector,moore,1,all
	#initial_board = initiate_CA_sector(n)
	#neighborhood_method = "moore"
	#radius = 1
	#update_method = "all"

	##sector,moore,1,random
	#initial_board = initiate_CA_sector(n)
	#neighborhood_method = "moore"
	#radius = 1
	#update_method = "random"

	##sector,moore,2,all
	initial_board = initiate_CA_sector(n)
	neighborhood_method = "moore"
	radius = 2
	update_method = "all"

	##sector,moore,2,random
	#initial_board = initiate_CA_sector(n)
	#neighborhood_method = "moore"
	#radius = 2
	#update_method = "random"

	###

	##sector,neumann,1,all
	#initial_board = initiate_CA_sector(n)
	#neighborhood_method = "neumann"
	#radius = 1
	#update_method = "all"

	##sector,neumann,1,random
	#initial_board = initiate_CA_sector(n)
	#neighborhood_method = "neumann"
	#radius = 1
	#update_method = "random"

	##sector,neumann,2,random
	#initial_board = initiate_CA_sector(n)
	#neighborhood_method = "neumann"
	#radius = 2
	#update_method = "random"

	##sector,neumann,2,all
	#initial_board = initiate_CA_sector(n)
	#neighborhood_method = "neumann"
	#radius = 2
	#update_method = "all"





	color_board(initial_board,ms)
	new_board,r,p,s = update_board(initial_board,neighborhood_method,radius,update_method,time_steps)
	color_board(new_board,ms)
	make_abundance_plot(time_steps,r,p,s)


main()

