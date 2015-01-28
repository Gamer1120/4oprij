package client;

import game.Board;
import game.Disc;
import game.strategy.ComputerPlayer;
import game.strategy.MinMaxStrategy;
import game.strategy.NaiveStrategy;
import game.strategy.SmartStrategy;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.HashMap;
import java.util.Map;

import server.ClientHandler;
import server.Server;

/**
 * client program for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class Client extends Thread {
	// The protocol, as discussed in our TI-2 group. For further explanation,
	// you can look at the protocol documentation.
	public static final String CONNECT = "CONNECT";
	public static final String QUIT = "QUIT";
	public static final String INVITE = "INVITE";
	public static final String ACCEPT_INVITE = "ACCEPT";
	public static final String DECLINE_INVITE = "DECLINE";
	public static final String MOVE = "MOVE";
	public static final String CHAT = "CHAT";
	public static final String REQUEST_BOARD = "REQUEST";
	public static final String REQUEST_LOBBY = "LOBBY";
	public static final String REQUEST_LEADERBOARD = "LEADERBOARD";
	public static final String ERROR = "ERROR";
	public static final String PING = "PING";
	// END OF PROTOCOL
	// CUSTOM COMMANDS
	public static final String HELP = "HELP";
	public static final String HINT = "HINT";
	public static final String DIFFICULTY = "DIFFICULTY";
	// END OF CUSTOM COMMANDS

	/**
	 * The features this client has.
	 */
	private static final String CLIENT_FEATURES = ClientHandler.CHAT + " "
			+ ClientHandler.CUSTOM_BOARD_SIZE + " " + ClientHandler.LEADERBOARD;

	/**
	 * The name of this client.
	 */
	private String clientName;

	/**
	 * The User Interface of this client.
	 */
	private ClientTUI mui;

	/**
	 * The Socket
	 */
	private Socket sock;
	/**
	 * The BufferedReader that will be used to communicate over the Socket.
	 */
	private BufferedReader in;
	/**
	 * The BufferedWriter that will be used to communicate over the Socket.
	 */
	private BufferedWriter out;
	/**
	 * While this boolean is true, it makes sure that commands are continuously
	 * read from the BufferedReader.
	 */
	private boolean loop;

	/**
	 * The Board this client uses for determining their move.
	 */
	private Board board;

	/**
	 * The enum to keep track of whether this client is connected or trying to
	 * connect.
	 */
	public enum Connection {
		FALSE, CONNECTING, TRUE
	}

	/**
	 * An enum to determine whether this client is connected.
	 */
	private Connection isConnected;
	/**
	 * The Player this client is.
	 */
	private ComputerPlayer computerPlayer;

	/**
	 * A boolean to determine whether the server has requested a move.
	 */
	private boolean moveRequested;
	/**
	 * A Map of invites this client is invited by. This map gets emptied every
	 * time a Game starts.
	 */
	private Map<String, Integer[]> invitedBy;
	/**
	 * A Map of invited this client sent. This map gets emptied every time a
	 * Game starts.
	 */
	private Map<String, Integer[]> invited;

	/**
	 * The number of this client in a game, as stored on the Server.
	 */
	private int myNumber;

	/**
	 * An array with a move. This is used if the move can't be made on the
	 * Board, and the Board needs to be requested from the Server.
	 */
	private int[] savedMove;

	/*@	private invariant sock != null;
	 	private invariant mui != null;
	 	private invariant in != null;
	 	private invariant out != null;
	  	private invariant invited != null;
	  	private invariant invitedBy != null;
	 */

	/**
	 * Constructs a client object and tries to make a Socket connection
	 * 
	 * @param host
	 *            The IP-adress of this client
	 * @param port
	 *            The port of this client
	 * @param muiArg
	 *            The ClientTUI for this client
	 * @throws IOException
	 *             When it can't get the socket's in or outputstream, or the
	 *             socket can't connect to the server.
	 */
	/*@ requires host != null;
	 	requires port >= 1 & port <= 65535;
	 	requires muiArg != null;
	 	ensures isConnected() == Connection.FALSE;
	 	ensures getBoard() == null;
	 */
	public Client(InetAddress host, int port, ClientTUI muiArg)
			throws IOException {
		this.mui = muiArg;
		this.sock = new Socket(host, port);
		this.in = new BufferedReader(new InputStreamReader(
				sock.getInputStream()));
		this.out = new BufferedWriter(new OutputStreamWriter(
				sock.getOutputStream()));
		this.isConnected = Connection.FALSE;
		this.invited = new HashMap<String, Integer[]>();
		this.invitedBy = new HashMap<String, Integer[]>();
		this.loop = true;
		this.board = null;
		this.moveRequested = false;
		this.computerPlayer = null;
		this.savedMove = null;
	}

	/**
	 * Sets up a player with the given name. If the name starts with "-N ", a
	 * ComputerPlayer with a NaiveStrategy is created instead, and if the name
	 * starts with "-S ", a ComputerPlayer with a SmartStrategy is created.
	 * 
	 * @param name
	 *            The String returned by askName.
	 */
	/*@ requires !name.equals("");
	 	requires name != null;
	 */
	public void setUpPlayer(String name) {
		String[] splitName = name.split("\\s+");
		if (splitName[0].equals("")) {
			isConnected = Connection.FALSE;
		} else {
			if (splitName[0].equals("-N")) {
				if (splitName.length == 1) {
					this.clientName = "NaivePlayer";
					this.computerPlayer = new ComputerPlayer(Disc.YELLOW,
							new NaiveStrategy());
				} else {
					this.clientName = splitName[1];
					this.computerPlayer = new ComputerPlayer(Disc.YELLOW,
							new NaiveStrategy());
				}
			} else if (splitName[0].equals("-S")) {
				if (splitName.length == 1) {
					this.clientName = "SmartPlayer";
					this.computerPlayer = new ComputerPlayer(Disc.YELLOW,
							new SmartStrategy());
				} else {
					this.clientName = splitName[1];
					this.computerPlayer = new ComputerPlayer(Disc.YELLOW,
							new SmartStrategy());
				}
			} else if (splitName[0].equals("-M")) {
				if (splitName.length == 1) {
					this.clientName = "MiniMaxPlayer";
					this.computerPlayer = new ComputerPlayer(Disc.YELLOW,
							new MinMaxStrategy());
				} else {
					this.clientName = splitName[1];
					this.computerPlayer = new ComputerPlayer(Disc.YELLOW,
							new MinMaxStrategy());
				}
			} else {
				this.clientName = splitName[0];
				this.computerPlayer = null;
			}
			isConnected = Connection.CONNECTING;
			sendMessage(CONNECT + " " + getClientName() + " " + CLIENT_FEATURES);
		}
	}

	/**
	 * This method reads the messages in the InputStream. Then, it decides which
	 * command was sent, and executes this command by calling the method created
	 * for it.
	 */
	@Override
	public void run() {
		while (loop) {
			String line = "";
			try {
				while (line.equals("")) {
					line = in.readLine();
				}
				/*
				 * Calling in.readLine() when the connection is lost gives an
				 * IOException, but when in.readLine() has already been called
				 * and the connection is lost in.readLine will result in null and
				 * input.equals() will result in an NullPointerException. If the
				 * connection is lost the client shuts down.
				 */
			} catch (IOException | NullPointerException e) {
				shutdown();
				break;
			}
			String[] serverMessage = line.split("\\s+");
			switch (serverMessage[0]) {
			case Server.ACCEPT_CONNECT:
				isConnected = Connection.TRUE;
				serverConnect(serverMessage);
				break;
			case Server.LOBBY:
				serverLobby(serverMessage);
				break;
			case Server.INVITE:
				serverInvite(serverMessage);
				break;
			case Server.DECLINE_INVITE:
				serverDecline(serverMessage);
				break;
			case Server.GAME_START:
				serverGameStart(serverMessage);
				break;
			case Server.GAME_END:
				serverGameEnd(serverMessage);
				break;
			case Server.REQUEST_MOVE:
				serverRequestMove(serverMessage);
				break;
			case Server.MOVE_OK:
				serverMoveOK(serverMessage);
				break;
			case Server.ERROR:
				mui.addErrorMessage(line.split(" ", 2)[1]);
				if (isConnected == Connection.CONNECTING) {
					isConnected = Connection.FALSE;
				}
				break;
			case Server.BOARD:
				board = toBoard(line);
				break;
			case Server.CHAT:
				mui.addChatMessage(line.split(" ", 2)[1]);
				break;
			case Server.LEADERBOARD:
				serverShowLeaderboard(serverMessage);
				break;
			case Server.PONG:
				mui.addPingMessage("Pong!");
				break;
			default:
				sendMessage(ERROR + " " + serverMessage[0]
						+ " Unknown command.");
				break;
			}
		}
	}

	/**
	 * This method sends a message to the ClientHandler using the OutputStream
	 * out.
	 * 
	 * @param msg
	 *            The message to be sent.
	 */
	//@ requires msg != null;
	public void sendMessage(String msg) {
		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			shutdown();
		}
	}

	//ACCEPTING FROM SERVER
	/**
	 * This method accepts the Server.CONNECT packet sent by the Server. When
	 * this method is called, it prints that a connection has been established
	 * with the Server, as well as the IP address and port of the Server. After
	 * this, it lists the features the Server has.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@	requires serverMessage != null & serverMessage[0].equals(Server.ACCEPT_CONNECT);
	private void serverConnect(String[] serverMessage) {
		mui.addConnectMessage("Successfully established connection to server: "
		// IP of the server
				+ sock.getRemoteSocketAddress().toString());
		mui.addFeaturesMessage("The features of this server are:"
				+ arrayToLine(serverMessage));
	}

	/**
	 * This method accepts the Server.LOBBY packet sent by the Server. When this
	 * method is called, it shows the client the other Clients that are
	 * currently in the lobby.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage != null & serverMessage[0].equals(Server.LOBBY);
	private void serverLobby(String[] serverMessage) {
		mui.addLobbyMessage("The people that are currently in the lobby are:"
				+ arrayToLine(serverMessage));
	}

	/**
	 * This method accepts the Server.INVITE packet sent by the Server. When
	 * this method is called, it adds the inviter (and to an inviterlist, and
	 * potentially, the custom board size. If the player isn't ingame, it will
	 * also show the client that they have been invited by that client.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage != null & serverMessage[0].equals(Server.INVITE);
	private void serverInvite(String[] serverMessage) {
		String opponentName = serverMessage[1];
		if (serverMessage.length == 2) {
			addServerInvite(opponentName);
			mui.addInviteMessage(opponentName
					+ " has invited you to a game of Connect4 (default boardsize)!");
			mui.addInviteMessage("Use \"ACCEPT " + opponentName
					+ "\" to accept this invite or \"DECLINE " + opponentName
					+ "\" to decline it.");
		} else if (serverMessage.length >= 4) {
			try {
				int boardX = Integer.parseInt(serverMessage[2]);
				int boardY = Integer.parseInt(serverMessage[3]);
				addServerInvite(opponentName, boardX, boardY);
				mui.addInviteMessage(opponentName
						+ " has invited you to a game of Connect4 with a custom Board size of "
						+ boardX + " x " + boardY + "!");
				mui.addInviteMessage("Use \"ACCEPT " + opponentName
						+ "\" to accept this invite or \"DECLINE "
						+ opponentName + "\" to decline it.");
			} catch (NumberFormatException e) {
				mui.addErrorMessage("The server just sent an invite with an invalid custom board size.");
				sendMessage(ERROR
						+ " "
						+ INVITE
						+ " Your server just sent me an invite with an invalid custom board size :(");
			}
		}
	}

	/**
	 * This method accepts the Server.DECLINE_INVITE packet. If the Server
	 * specified a person, the person will be removed from the list of people
	 * this client has invited.
	 * 
	 * @param serverMessage
	 *            The full messsage the server sent.
	 */
	//@ requires serverMessage != null & serverMessage[0].equals(Server.DECLINE_INVITE);
	private void serverDecline(String[] serverMessage) {
		if (serverMessage.length > 1) {
			invited.remove(serverMessage[1]);
			mui.addInviteMessage("The invite you sent to " + serverMessage[1]
					+ " got declined.");
		} else {
			mui.addInviteMessage("The server just tried to decline one of your invites, but it didn't send who declined yours.");
			sendMessage(ERROR + " " + serverMessage[0]
					+ " Your server didn't send me who declined the invite.");
		}
	}

	/**
	 * This method accepts the Server.GAME_START packet sent by the Server. When
	 * this method is called, it will show the client that a the game is
	 * started. The client is set to being in-game, and a new Board is created.
	 * The size of the Board is dependant on the size sent in the invite (the
	 * Boardsizes of the invites are saved in a HashMap).
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	/*@ requires serverMessage != null & serverMessage[0].equals(Server.GAME_START);
	 	ensures board != null;
	 	ensures myNumber != -1;
	 */
	private void serverGameStart(String[] serverMessage) {
		if (serverMessage[1].equals(getClientName())) {
			myNumber = 1;
			mui.addGameMessage("A game between you and " + serverMessage[2]
					+ " has started!");
			Integer[] boardSize = invitedBy.get(serverMessage[2]);

			board = new Board(boardSize[1], boardSize[0]);
		} else {
			myNumber = 2;
			mui.addGameMessage("A game between you and " + serverMessage[1]
					+ " has started!");
			Integer[] boardSize = invited.get(serverMessage[1]);
			board = new Board(boardSize[1], boardSize[0]);
		}
		mui.addBoard();
		mui.addGameMessage("You are YELLOW");
	}

	/**
	 * This method accepts the Server.GAME_END packet sent by the Server. When
	 * this method is called, it will set the client to no longer being in-game.
	 * It will also show the client who won the game, or if the game was a draw.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	/*@	requires serverMessage != null & serverMessage[0].equals(Server.GAME_END);
		ensures this.board == null;
	*/
	private void serverGameEnd(String[] serverMessage) {
		this.board = null;
		if (serverMessage.length > 2) {
			mui.addGameMessage("The winner is: " + serverMessage[2]);
		} else if (serverMessage.length == 2) {
			if (serverMessage[1].equals(ClientHandler.DRAW)) {
				mui.addGameMessage("The game was a draw!");
			} else {
				mui.addGameMessage("The game has ended. Reason:"
						+ arrayToLine(serverMessage));
			}
		}
	}

	/**
	 * This method accepts the Server.MOVE packet sent by the Server. When this
	 * method is called, it will request a move from the Player. If the Player
	 * is a HumanPlayer, the GameView will be used to ask for a move. If the
	 * Player is a ComputerPlayer, the determineMove() method from the
	 * ComputerPlayer is used instead.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	/*@ requires serverMessage != null & serverMessage[0].equals(Server.REQUEST_MOVE);
	 	ensures moveRequested;
	 */
	private void serverRequestMove(String[] serverMessage) {
		if (computerPlayer == null) {
			moveRequested = true;
			mui.addMoveMessage("Please enter a move.");
			;
		} else {
			int move = computerPlayer.determineMove(board.deepCopy());
			sendMessage(MOVE + " " + move);
		}
	}

	/**
	 * This method accepts the Server.MOVE_OK packet sent by the Server. When
	 * this method is called, it will update the Board by inserting the Disc for
	 * the Player that was given in the packet. If it can't insert the Disc, it
	 * will request the Board and try to insert the Disc once again.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage != null & serverMessage[0].equals(Server.MOVE_OK);
	private void serverMoveOK(String[] serverMessage) {
		int move = -1;
		try {
			move = Integer.parseInt(serverMessage[2]);
		} catch (NumberFormatException e) {
			mui.addErrorMessage("Server did not send a valid move. TERMINATING.");
			sendMessage(ERROR + " " + Server.MOVE_OK + " Couldn't parse move.");
			shutdown();
		}
		if (checkMove(move)) {
			makeMove(Integer.parseInt(serverMessage[1]), move);
			mui.addBoard();
		} else {
			mui.addErrorMessage("Couldn't do the move, requesting board from server");
			savedMove = new int[] { Integer.parseInt(serverMessage[1]), move };
			clientRequestBoard();
		}
	}

	/**
	 * If the server sent a valid Leaderboard, this method adds the formatted
	 * leaderboard to the View.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage != null & serverMessage[0].equals(Server.LEADERBOARD);
	private void serverShowLeaderboard(String[] serverMessage) {
		if ((serverMessage.length - 1) % 5 == 0) {
			int amountOfPlayers = (serverMessage.length - 1) / 5;
			//@ loop_invariant 0 <= i & i <= amountOfPlayers;
			for (int i = 0; i < amountOfPlayers; i++) {
				mui.addLeaderBoardLine(serverMessage[((i * 5) + 5)],
						serverMessage[((i * 5) + 1)],
						serverMessage[((i * 5) + 2)],
						serverMessage[((i * 5) + 3)],
						serverMessage[((i * 5) + 4)]);
			}
		} else {
			mui.addErrorMessage("Didn't get a valid Leaderboard from the Server.");
			sendMessage(ERROR + " " + Server.LEADERBOARD
					+ " Didn't get a valid Leaderboard from your Server :(");
		}
	}

	//END ACCEPTING FROM SERVER

	//ACCEPTING FROM VIEW
	/**
	 * Shows the commands that are available. In case the client is in-game,
	 * different commands are shown than when he's not.
	 */
	public void clientHelp() {
		if (isIngame()) {
			mui.addHelpMessage("Available commands are: " + Client.MOVE
					+ " <column>, " + Client.HINT + ", " + Client.PING + ", "
					+ Client.HELP + ", " + Client.DIFFICULTY + " <number>"
					+ " and " + Client.QUIT + ".");
		} else {
			mui.addHelpMessage("Available commands are: " + Client.INVITE
					+ " <player>, " + Client.ACCEPT_INVITE + " <player>, "
					+ Client.DECLINE_INVITE + " <player>, " + Client.CHAT
					+ " <message>, " + Client.REQUEST_LOBBY + ", "
					+ Client.REQUEST_LEADERBOARD + ", " + Client.PING + ", "
					+ Client.HELP + ", " + Client.DIFFICULTY + " <number>"
					+ " and " + Client.QUIT + ".");
		}
	}

	/**
	 * Forwards the move the player just made to the server, if the move was
	 * valid, and there was a move requested.
	 * 
	 * @param input
	 *            The raw message the view sent.
	 * @param splitInput
	 *            The message the view sent, split up in an array.
	 */
	/*@	requires input != null & !input.equals("");
	 	requires splitInput != null & !splitInput.equals("");
	 */
	public void clientMove(String input, String[] splitInput) {
		if (moveRequested) {
			moveRequested = false;
			if (splitInput.length == 2) {
				try {
					Integer.parseInt(splitInput[1]);
				} catch (NumberFormatException e) {
					mui.addErrorMessage("Please enter a valid move after MOVE.");
				}
				sendMessage(input);
			} else {
				mui.addErrorMessage("Please enter exactly one argument after MOVE.");
			}
		} else {
			mui.addErrorMessage("There was no move requested.");
		}
	}

	/**
	 * Forwards the invite the player just made to the server, if the player
	 * added a name to invite. It saves the invite in the HashMap made for this.
	 * This method also supports custom board sizes.
	 * 
	 * @param input
	 *            The raw message the view sent.
	 * @param splitInput
	 *            The message the view sent, split up in an array.
	 */
	/*@	requires input != null & !input.equals("");
		requires splitInput != null & !splitInput.equals("");
	 */
	public void clientInvite(String input, String[] splitInput) {
		if (splitInput.length >= 4) {
			try {
				addClientInvite(splitInput[1], Integer.parseInt(splitInput[2]),
						Integer.parseInt(splitInput[3]));
				sendMessage(input);
				mui.addInviteMessage("Tried to invite: " + splitInput[1]
						+ " with the specified custom board size.");
			} catch (NumberFormatException e) {
				mui.addErrorMessage("Please specify the BoardX and BoardY as integers. Invite failed.");
			}
		} else if (splitInput.length >= 2) {
			addClientInvite(splitInput[1]);
			sendMessage(input);
			mui.addInviteMessage("Tried to invite: " + splitInput[1]
					+ " with default board size.");
		} else {
			mui.addErrorMessage("Invalid arguments, couldn't send invite");
		}
	}

	/**
	 * Forwards that an invite has been accepted to the server, as well as whose
	 * invite got accepted, provided that the player entered a name.
	 * 
	 * @param input
	 *            The raw message the server sent.
	 * @param splitInput
	 *            The message the view sent, split up in an array.
	 */
	/*@	requires input != null & !input.equals("");
		requires splitInput != null & !splitInput.equals("");
	 */
	public void clientAccept(String input, String[] splitInput) {
		if (splitInput.length == 2) {
			sendMessage(Client.ACCEPT_INVITE + " " + splitInput[1]);
		} else {
			mui.addErrorMessage("Please use ACCEPT <name> to accept an invite.");
		}
	}

	/**
	 * Forwards the rejected invite to the Server, if the player specified whose
	 * invite to decline.
	 * 
	 * @param input
	 *            The raw message the server sent.
	 * @param splitInput
	 *            The message the view sent, split up in an array.
	 */
	/*@	requires input != null & !input.equals("");
		requires splitInput != null & !splitInput.equals("");
	 */
	public void clientDecline(String input, String[] splitInput) {
		if (splitInput.length == 2) {
			removeServerInvite(splitInput[1]);
			sendMessage(input);
			mui.addInviteMessage("Tried to decline " + splitInput[1]
					+ "'s invite.");
		} else {
			mui.addErrorMessage("Please use DECLINE <name> to decline an invite.");
		}
	}

	/**
	 * Gives the client a suggested move (does not actually do the move) using
	 * it's view.
	 */
	/*@ pure */public void clientHint() {
		if (isIngame()) {
			mui.addHintMessage(new MinMaxStrategy().determineMove(
					board.deepCopy(), Disc.YELLOW));
		} else {
			mui.addErrorMessage("You're not in-game.");
		}
	}

	/**
	 * Method to request the board from the server.
	 */
	public void clientRequestBoard() {
		sendMessage(REQUEST_BOARD);
	}

	/**
	 * Method to set the difficulty of a MinMaxStrategy. The difficulty is the
	 * amount of turns the game.strategy will think ahead.
	 * 
	 * @param input
	 *            The raw message the view sent.
	 */
	public void clientDifficulty(String input) {
		if (computerPlayer.getStrategy() instanceof MinMaxStrategy) {
			try {
				int depth = Integer.parseInt(input);
				((MinMaxStrategy) computerPlayer.getStrategy()).setDepth(depth);
				mui.addDifficultyMessage(true);
			} catch (NumberFormatException e) {
				mui.addErrorMessage("Can't parse difficulty");
				mui.addDifficultyMessage(false);
			}
		} else {
			mui.addErrorMessage("Only the difficulty of the MinMaxPlayer can be changed");
			mui.addDifficultyMessage(false);
		}
	}

	//END ACCEPTING FROM VIEW

	//CLIENT GETTERS
	/**
	 * This method returns whether the client is connected to a server.
	 * 
	 * @return true if the client is connected to a server.
	 */
	/*@ pure */public Connection isConnected() {
		return isConnected;
	}

	/**
	 * This method returns whether the client is ingame.
	 * 
	 * @return true if the client is ingame.
	 */
	/*@ pure */public boolean isIngame() {
		return board != null;
	}

	/**
	 * This method returns the name of this client.
	 * 
	 * @return The name of this client.
	 */
	/*@ pure */public String getClientName() {
		return clientName;
	}

	/**
	 * This method returns the Board object stored for this client.
	 * 
	 * @return The Board object stored for this client.
	 */
	//@ requires isIngame();
	/*@ pure */public Board getBoard() {
		return board;
	}

	//END CLIENT GETTERS

	//USEFUL METHODS
	/**
	 * Checks if a move is valid on the stored Board.
	 * 
	 * @param move
	 *            The move to be made.
	 * @return If that move is valid.
	 */
	//@ requires isIngame();
	/*@ pure */private boolean checkMove(int move) {
		return board.isField(move) && board.isEmptyField(move);
	}

	/**
	 * Makes a move on the Board.
	 * 
	 * @param player
	 *            The number of the player.
	 * @param col
	 *            The column to throw the Disc in.
	 */
	//@ requires isIngame();
	private void makeMove(int player, int col) {
		if (player == myNumber) {
			board.insertDisc(col, Disc.YELLOW);
		} else {
			board.insertDisc(col, Disc.RED);
		}
		savedMove = null;
	}

	/**
	 * This method makes a Board out of the packet the server sends when the
	 * Board is requested.
	 * 
	 * @param line
	 *            The Boardpacket the Server sent.
	 * @return A new Board object with the Board as sent by the Server.
	 */
	//@ requires line != null;
	//@ requires isIngame();
	public Board toBoard(String line) {
		String[] protocol = line.split(" ");
		Board serverBoard = null;
		if (myNumber == 1) {
			try {
				serverBoard = makeBoard(Integer.parseInt(protocol[2]),
						Integer.parseInt(protocol[1]), Disc.YELLOW, Disc.RED,
						line.split(" "));
			} catch (NumberFormatException e) {
				mui.addErrorMessage("Server sent a wrong board. TERMINATING.");
				sendMessage(ERROR + " " + Server.BOARD
						+ " Couldn't parse Board. TERMINATING.");
				shutdown();
			}
			board = serverBoard;
			makeMove(savedMove[0], savedMove[1]);
			mui.addGameMessage("Succesfully received the board from the server");
			mui.addBoard();
		} else if (myNumber == 2) {
			try {
				serverBoard = makeBoard(Integer.parseInt(protocol[2]),
						Integer.parseInt(protocol[1]), Disc.RED, Disc.YELLOW,
						line.split(" "));
			} catch (NumberFormatException e) {
				mui.addErrorMessage("Server sent a wrong board. TERMINATING.");
				sendMessage(ERROR + " " + Server.BOARD
						+ " Couldn't parse Board. TERMINATING.");
				shutdown();
			}
			board = serverBoard;
			makeMove(savedMove[0], savedMove[1]);
			mui.addGameMessage("Succesfully received the board from the server");
			mui.addBoard();
		} else {
			mui.addErrorMessage("Couldn't determine player.");
		}
		board = serverBoard;
		makeMove(savedMove[0], savedMove[1]);
		mui.addGameMessage("Succesfully received the board from the server");
		mui.addBoard();
		return serverBoard;
	}

	/**
	 * This method is used by toBoard to create a Board.
	 * 
	 * @param rows
	 *            The amount of rows the Board has.
	 * @param columns
	 *            The amount of columns the Board has.
	 * @param firstDisc
	 *            The Disc the first player uses.
	 * @param secondDisc
	 *            The Disc the second player uses.
	 * @param serverMessage
	 *            The board as sent by the server.
	 * @return A valid Board constructed from these parameters.
	 */
	//@ requires isIngame();
	public Board makeBoard(int rows, int columns, Disc firstDisc,
			Disc secondDisc, String[] serverMessage) {
		Board serverBoard = new Board(rows, columns);
		int i = 3;
		//@ loop_invariant row >= -1 & row < serverBoard.getRows();
		for (int row = rows - 1; row >= 0; row--) {
			//@ loop_invariant col >= 0 & col <= serverBoard.getColumns();
			for (int col = 0; col < columns; col++) {
				if (Integer.parseInt(serverMessage[i]) == 0) {
					//Disc.EMPTY
					serverBoard.setField(row, col, Disc.EMPTY);
				} else if (Integer.parseInt(serverMessage[i]) == 1) {
					//Disc.YELLOW
					serverBoard.setField(row, col, firstDisc);
				} else if (Integer.parseInt(serverMessage[i]) == 2) {
					//Disc.RED
					serverBoard.setField(row, col, secondDisc);
				}
				i++;
			}
		}
		return serverBoard;
	}

	/**
	 * This method is used to convert an Stringarray to a single String.
	 * 
	 * @param array
	 *            The array to convert.
	 * @return The array converted to one line.
	 */
	//@ requires array != null;
	public String arrayToLine(String[] array) {
		String retLine = "";
		//@ loop_invariant i >= 1 & i <= array.length;
		for (int i = 1; i < array.length; i++) {
			retLine += " " + array[i];
		}
		return retLine;
	}

	//END USEFUL METHODS

	//HANDLE INVITES
	/**
	 * Method to add an invite to the list of people this client has invited.
	 * 
	 * @param name
	 *            The name this client just invited.
	 */
	/*@ requires !name.equals("");
		requires name != null;
	*/
	public void addClientInvite(String name) {
		addClientInvite(name, 7, 6);
	}

	/**
	 * Method to add an invite to the list of people this client has invited
	 * with a custom Board size.
	 * 
	 * @param name
	 *            The name this client just invited.
	 * @param BoardX
	 *            The custom Board size's X value.
	 * @param BoardY
	 *            The custom Board size's Y value.
	 */
	/*@ requires !name.equals("");
	 	requires name != null;
	 	requires BoardX > 0;
	 	requires BoardY > 0;
	 */
	public void addClientInvite(String name, int BoardX, int BoardY) {
		invited.put(name, new Integer[] { BoardX, BoardY });
	}

	/**
	 * Method to add an invite to the list of people this client has been
	 * invited by.
	 * 
	 * @param name
	 *            The name this client just got invited by.
	 */
	public void addServerInvite(String name) {
		addServerInvite(name, 7, 6);
	}

	/**
	 * Method to add an invite to the list of people this client has been
	 * invited by with a custom Board size.
	 * 
	 * @param name
	 *            The name this client just got invited by.
	 * @param BoardX
	 *            The custom Board size's X value.
	 * @param BoardY
	 *            The custom Board size's Y value.
	 */
	public void addServerInvite(String name, int BoardX, int BoardY) {
		invitedBy.put(name, new Integer[] { BoardX, BoardY });
	}

	/**
	 * Method to remove an invite from the list of people this client has
	 * invited. It's called when the server sends a Server.DECLINE_INVITE
	 * packet.
	 * 
	 * @param name
	 *            The name of the person who declined the invite.
	 */
	public void removeServerInvite(String name) {
		invited.remove(name);
	}

	//END HANDLING INVITES

	/**
	 * This method closes the Socket connection and exits the program. On a side
	 * note, before it does this, it also sets the loop variable for this client
	 * to false.
	 */
	public void shutdown() {
		if (loop) {
			loop = false;
			mui.addMessage("Shutting down...");
			sendMessage(Client.QUIT + " Shutdown");
			try {
				sock.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
			System.exit(0);
		}
	}
}
