package clientserver;

import game.Board;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.HashMap;
import java.util.HashSet;

// TODO: Auto-generated Javadoc
/**
 * P2 prac wk5. <br>
 * Server. A Thread class that listens to a socket connection on a specified
 * port. For every socket connection with a Client, a new ClientHandler thread
 * is started.
 * 
 * @author Theo Ruys
 * @version 2005.02.21
 */
public class Server extends Thread {
	// PROTOCOL
	/** The Constant ACCEPT_CONNECT. */
	public static final String ACCEPT_CONNECT = "OK";

	/** The Constant ERROR. */
	public static final String ERROR = "ERROR";

	/** The Constant LOBBY. */
	public static final String LOBBY = "LOBBY";

	/** The Constant INVITE. */
	public static final String INVITE = "INVITE";

	/** The Constant GAME_START. */
	public static final String GAME_START = "START";

	/** The Constant GAME_END. */
	public static final String GAME_END = "END";

	/** The Constant REQUEST_MOVE. */
	public static final String REQUEST_MOVE = "REQUEST";

	/** The Constant MOVE_OK. */
	public static final String MOVE_OK = "MOVE";

	/** The Constant BOARD. */
	public static final String BOARD = "BOARD";

	/** The Constant CHAT. */
	public static final String CHAT = "CHAT";

	/** The Constant LEADERBOARD. */
	public static final String LEADERBOARD = "LEADERBOARD";
	// END OF PROTOCOL

	public static final String FEATURES = Features.CHAT + " "
			+ Features.CUSTOM_BOARD_SIZE;
	/** The port. */
	private int port;

	/** The mui. */
	private MessageUI mui;
	// TODO: feature lijst

	/** The threads. */
	private HashSet<ClientHandler> threads;

	/** The invites. */
	// TODO: Observable class
	private HashMap<String[], Integer[]> invites;

	/**
	 * Constructs a new Server object.
	 *
	 * @param portArg
	 *            the port arg
	 * @param muiArg
	 *            the mui arg
	 */
	/*@ requires portArg >= 1 & portArg <= 65535;
		requires muiArg != null;
	 */
	public Server(int portArg, MessageUI muiArg) {
		this.port = portArg;
		this.mui = muiArg;
		this.threads = new HashSet<ClientHandler>();
		this.invites = new HashMap<String[], Integer[]>();
	}

	/**
	 * Listens to a port of this Server if there are any Clients that would like
	 * to connect. For every new socket connection a new ClientHandler thread is
	 * started that takes care of the further communication with the Client.
	 */
	public void run() {
		try {
			@SuppressWarnings("resource")
			ServerSocket ss = new ServerSocket(port);
			while (true) {
				Socket s = ss.accept();
				ClientHandler ch = new ClientHandler(this, s);
				addHandler(ch);
				ch.start();
			}
		} catch (IOException e) {
			// TODO: betere error handling
			e.printStackTrace();

		}
	}

	/**
	 * Sends a message using the collection of connected ClientHandlers to all
	 * connected Clients.
	 * 
	 * @param msg
	 *            message that is send
	 */
	//@ requires msg != null;
	public void broadcast(String msg) {
		synchronized (threads) {
			for (ClientHandler ch : threads) {
				if (ch.connected()) {
					ch.sendMessage(msg);
				}
			}
			mui.addMessage("Broadcast: " + msg);
		}
	}

	/**
	 * Sends a message using the collection of connected ClientHandlers to all
	 * connected Clients without a game.
	 */
	public void broadcastLobby() {
		synchronized (threads) {
			for (ClientHandler ch : threads) {
				if (!ch.inGame()) {
					ch.sendMessage(LOBBY + getLobby());
				}
			}
			mui.addMessage("Lobby:" + getLobby());
		}
	}

	/**
	 * Sends a message using the collection of connected ClientHandlers to all
	 * connected Clients with the chat feature.
	 * 
	 * @param msg
	 *            message that is send
	 */
	/*@ requires msg != null;
		requires msg.startsWith(CHAT);
	 */
	public void broadcastChat(String msg) {
		synchronized (threads) {
			for (ClientHandler ch : threads) {
				if (ch.connected() && ch.hasChat()) {
					ch.sendMessage(msg);
				}
			}
			mui.addMessage("Broadcast: " + msg);
		}
	}

	/**
	 * Print the message on the server gui.
	 *
	 * @param msg
	 *            message that is send
	 */

	//@ requires msg != null;
	public void print(String msg) {
		mui.addMessage(msg);
	}

	/**
	 * Checks if the name isn't already in use.
	 *
	 * @param name
	 *            the name
	 * @return true, if successful
	 */
	/*@ pure */public boolean nameExists(String name) {
		synchronized (threads) {
			boolean available = false;
			for (ClientHandler ch : threads) {
				if (name.equals(ch.getClientName())) {
					available = true;
					break;
				}
			}
			return available;
		}
	}

	/**
	 * Gets the client.
	 *
	 * @param name
	 *            the name
	 * @return the client
	 */
	// TODO: aanpassen voor Game of weghalen
	/*@ requires name != null;
		requires nameExists(name);
	 */
	/*@ pure */public ClientHandler getClient(String name) {
		synchronized (threads) {
			ClientHandler client = null;
			for (ClientHandler ch : threads) {
				if (ch.getClientName().equals(name)) {
					client = ch;
					break;
				}
			}
			return client;
		}
	}

	/**
	 * Sends a message using the collection of connected ClientHandlers to the
	 * Client with the specified name.
	 *
	 * @param name
	 *            name of the client
	 * @param msg
	 *            message that is send
	 */
	/*@ requires name != null;
		requires nameExists(name);
		requires msg != null;
	 */
	public void sendMessage(String name, String msg) {
		getClient(name).sendMessage(msg);
		mui.addMessage("Server send message to " + name + ": " + msg);
	}

	/**
	 * Checks wether the client with the specified name is in a game.
	 *
	 * @param name
	 *            name of the client
	 * @return true, if successful
	 */
	/*@ requires name != null;
		requires nameExists(name);
	*/
	/*@ pure */public boolean inGame(String name) {
		return getClient(name).inGame();
	}

	/**
	 * Generate board.
	 *
	 * @param name
	 *            the name
	 * @param invited
	 *            the invited
	 */
	/*@ requires name != null;
		requires nameExists(name);
		requires isInvited(name, invited);
	*/
	public void generateBoard(String name, String invited) {
		synchronized (invites) {
			Board board = null;
			for (String[] invite : invites.keySet()) {
				if (invite[0].equals(name) && invite[1].equals(invited)) {
					Integer[] boardSize = invites.get(invite);
					board = new Board(boardSize[1].intValue(),
							boardSize[0].intValue());
					break;
				}
			}
			setBoard(name, board);
			setBoard(invited, board);
		}
	}

	/**
	 * Sends the board to use for the game so both clientHandlers are using the
	 * same board.
	 *
	 * @param name
	 *            name of the client
	 * @param board
	 *            board that is send
	 */
	/*@ requires name != null;
		requires nameExists(name);
	*/
	private void setBoard(String name, Board board) {
		// TODO: Game maken inplaats van bord
		getClient(name).setBoard(board);
		mui.addMessage("Server set board for " + name);
	}

	/**
	 * Checks if the name isn't already in use.
	 *
	 * @param name
	 *            the name
	 * @return true, if successful
	 */
	/*@ requires name != null;
		requires nameExists(name);
	*/
	/*@ pure */public boolean hasCustomBoardSize(String name) {
		synchronized (threads) {
			boolean available = false;
			for (ClientHandler ch : threads) {
				if (name.equals(ch.getClientName()) && ch.hasCustomBoardSize()) {
					available = true;
					break;
				}
			}
			return available;
		}
	}

	/**
	 * Sends an string with the connected client names that aren't playing a
	 * game.
	 *
	 * @return the lobby
	 */
	/*@ pure */public String getLobby() {
		synchronized (threads) {
			String clients = "";
			for (ClientHandler ch : threads) {
				if (!ch.inGame() && ch.connected()) {
					clients += " " + ch.getClientName();
				}
			}
			return clients;
		}
	}

	/**
	 * Add a ClientHandler to the collection of ClientHandlers.
	 * 
	 * @param handler
	 *            ClientHandler that will be added
	 */
	/*@ requires handler != null;
	 */
	// TODO: ensure de privates
	public void addHandler(ClientHandler handler) {
		synchronized (threads) {
			threads.add(handler);
		}
	}

	/**
	 * Remove a ClientHandler from the collection of ClientHanlders.
	 * 
	 * @param handler
	 *            ClientHandler that will be removed
	 */
	//@ requires handler != null;
	public void removeHandler(ClientHandler handler) {
		synchronized (threads) {
			threads.remove(handler);
		}
	}

	/**
	 * Add the names of the inviting and the invited client in a list.
	 *
	 * @param name
	 *            name of the inviting client
	 * @param invited
	 *            name of the invited client
	 * @param boardX
	 *            the board x
	 * @param boardY
	 *            the board y
	 */
	/*@ requires name != null;
		requires nameExists(name);
		requires invited != null;
		requires nameExists(invited);
		requires boardX > 0;
		requires boardY > 0;
	*/
	public void addInvite(String name, String invited, int boardX, int boardY) {
		synchronized (invites) {
			invites.put(new String[] { name, invited }, new Integer[] { boardX,
					boardY });
		}
	}

	/**
	 * Checks whether the client is invited by the client with the specified
	 * name.
	 *
	 * @param name
	 *            the name of the client that send the invite
	 * @param invited
	 *            the name of the client that received the invite
	 * @return true, if is invited
	 */
	/*@ requires name != null;
		requires nameExists(name);
		requires invited != null;
		requires nameExists(invited);;
	*/
	/*@ pure */public boolean isInvited(String name, String invited) {
		synchronized (invites) {
			boolean retBool = false;
			for (String[] invite : invites.keySet()) {
				if (invite[0].equals(name) && invite[1].equals(invited)) {
					retBool = true;
					break;
				}
			}
			return retBool;
		}
	}

	/**
	 * Removes all invites of the client with the specified name.
	 * 
	 * @param name
	 *            the name of the client
	 */
	/*@ requires name != null;
		requires nameExists(name);
	*/
	public void removeInvite(String name) {
		synchronized (invites) {
			for (String[] invite : invites.keySet()) {
				if (invite[0].equals(name) || invite[1].equals(name)) {
					invites.remove(invite);
				}
			}
		}
	}

	/**
	 * Removes the invite of the client with the specified name.
	 * 
	 * @param name
	 *            the name of the client
	 * @param invited
	 *            the name of the invited client
	 */
	/*@ requires name != null;
		requires nameExists(name);
		requires invited != null;
		requires nameExists(invited);;
	*/
	public void removeInvite(String name, String invited) {
		synchronized (invites) {
			for (String[] invite : invites.keySet()) {
				if (invite[0].equals(name) && invite[1].equals(invited)) {
					invites.remove(invite);
					break;
				}
			}
		}
	}
} // end of class Server
