# Réalisation spatiale du graphe existant

## 1. Objet

La 3D est une réalisation spatiale des choix du jeu existant. Le joueur se déplace
avec les touches et sélectionne un choix en atteignant son point d'interaction. Le moteur Lean
résout ce choix avec les règles et les dés existants.

La position, la caméra, l'éclairage et les animations sont des données de
présentation. Elles n'interviennent ni dans les dégâts, ni dans les jets, ni dans
les probabilités de transition.

## 2. Graphe logique

Soit S l'ensemble des états logiques. Pour chaque état s, A(s) est l'ensemble fini
des choix disponibles. Pour a appartenant à A(s), K(s,a,·) est la distribution
des conséquences du choix, déterminée par la machine.

Un choix et son résultat aléatoire sont distincts. Par exemple, le joueur peut
choisir de tenter une escalade ; le moteur choisit la branche réussite ou échec
en appliquant le jet prévu.

Dans le projet :

- Adventure, Scene et Choice décrivent les choix.
- Outcome décrit goto, roll ou fight et leurs conséquences.
- Game.inputs énumère les commandes actuellement autorisées.
- step : Game → Input → Roll (Game × List Report) exécute ces commandes.
- Graph.step est le noyau utilisé pour l'analyse probabiliste des aventures.

L'état du graphe d'aventure conserve la scène et les HP. Il distingue les états
terminaux ended, dead et stalled. Ces définitions restent celles du projet.

## 3. État du monde et projection

On représente un état du monde par w = (s,y). La composante s est l'état du
moteur. La composante y contient la position 3D, l'orientation de la caméra et
les autres données visuelles.

La projection α est définie par α(s,y) = s.

Un déplacement produit (s,y) → (s,y') et satisfait :

    α(s,y') = α(s,y).

Cette propriété concerne aussi l'attente, le changement d'orientation, les
animations de lumière, l'ouverture du journal et le redimensionnement de la
fenêtre. Ces opérations n'envoient aucune commande de jeu au serveur.

Le temps physique t sert au mouvement et aux animations. Il n'est pas ajouté
à l'état probabiliste de l'aventure. Attendre ne cause pas de jet ni de dégâts.

La position x(t) appartient à une région bornée de R³. Entre deux sélections,
sa vitesse est déterminée par les touches et l'orientation de la caméra. Le
déplacement est contraint à l'aire navigable. Dans l'implémentation, le temps
est échantillonné à chaque image ; le pas est borné et le segment parcouru est
testé contre les zones d'interaction. Aucun corps d'infinitésimaux n'est requis.

## 4. Objets, personnages et commandes

Pour une vue du moteur v, on construit l'ensemble P(v) des points d'interaction.
Chaque point p possède une commande β(p) copiée telle quelle depuis la vue.

À une scène correspond un point par Choice autorisé. En combat, un point
correspond à une commande de manœuvre et de cible autorisée. Une défense est
également une commande et possède son point.

Un point est matérialisé par un objet du récit : sentier, échelle, escalier,
barque, passage dans l'eau, fenêtre, porte réelle, coffre, lampe ou personnage.
Les manœuvres de combat sont matérialisées par une arme ou un bouclier ; leurs
étiquettes indiquent exactement la manœuvre et la cible. Les adversaires sont
représentés séparément, avec leur nom et leurs HP fournis par le moteur.

Une fonction d'habillage h(v,p) choisit une représentation visuelle à partir du
texte. Elle ne modifie jamais β. L'implémentation utilise une bibliothèque de
formes procédurales et des indices lexicaux, avec un sentier comme repli. Les PNJ
reconnus dans le récit sont aussi affichés ; cette reconnaissance ne constitue
pas une compréhension exhaustive de tout récit généré. Un PNJ décoratif ne
possède aucune action implicite : parler exige un Choice offert par le moteur.

Les textes, les coordonnées et les images ne sont jamais utilisés pour inventer
une commande ou une destination. Deux choix qui portent le même texte restent
distincts si leurs commandes diffèrent.

Le contrat sur les interactions est :

    { β(p) | p ∈ P(v) } = A(α(w)).

L'implémentation utilise un point par commande, sans doublon. Le constructeur
refuse une vue incomplète ou ambiguë au lieu de supprimer silencieusement un choix.
Il ignore toute commande présentée dans les métadonnées mais absente de inputs.

## 5. Accessibilité spatiale

Notons A3D(w) l'ensemble des commandes que l'on peut sélectionner depuis w par
un déplacement autorisé, sans sélectionner préalablement une autre commande.

Le contrat de navigation est :

    A3D(w) = A(α(w)).

Ce contrat porte sur les états jouables, après l'initialisation begin, quand la
vue est prête. Les écrans de titre et les requêtes en cours ne sont pas des
états de sélection. Dans un état terminal, les deux ensembles sont vides.

Il comprend deux obligations :

1. Absence de raccourci : aucune trajectoire ne déclenche un choix supplémentaire.
2. Complétude : chaque choix disponible est accessible physiquement.

La réalisation utilisée est une aire circulaire convexe, avec des points d'interaction séparés
sur son pourtour. Le rayon augmente avec le nombre de points. Le décor extérieur
ne bloque pas les déplacements. Les personnages de combat sont des représentations
visuelles et ne créent pas d'obstacles ou d'attaques physiques supplémentaires.

Le joueur apparaît à l'intérieur de l'aire. Une trajectoire directe permet
d'atteindre chaque point depuis ce point. Les tests exécutent le code de mouvement
et de franchissement sur des dispositions de 1 à 100 points.

La zone d'activation de chaque point est un disque de rayon 0,72. À moins de
2,1 unités, E sélectionne le point le plus proche. Les disques d'activation par
contact restent séparés. Un franchissement est détecté sur le segment entre deux positions, pas uniquement
à la position finale d'une image. Une image lente ne doit donc pas permettre de
traverser une zone d'interaction sans la déclencher.

## 6. Résolution d'un choix

Quand la zone d'un point est atteinte, ou que E est pressé à proximité, le navigateur transmet β(p) à /api/input. Le moteur
applique step. Il fournit ensuite la nouvelle vue et les rapports.

Pendant la requête et la présentation des rapports, le navigateur ne sélectionne
pas un deuxième point. Une nouvelle scène remet le joueur au point d'apparition ;
un retour vers la même scène est une nouvelle visite et produit aussi cette remise
à l'entrée. Une réponse refusée ne provoque pas une boucle de requêtes automatiques.

Dans le modèle probabiliste, le contrat est :

    P(α(W_après) = s' | W_avant = w, commande a) = K(α(w),a,s').

Le rendu ne tire aucun dé. Les animations de combat présentent les résultats du
serveur. La position devant un point de combat ne modifie pas la portée d'une
arme, l'esquive, les dégâts ou l'ordre des actions.

Pour une graine et une suite de commandes identiques, le jeu 3D et le jeu précédent
produisent les mêmes états logiques et les mêmes rapports.

Notons τn l'instant de la n-ième sélection et an la commande sélectionnée.
Entre τn et τn+1, l'état logique ne change pas. À la résolution de an, le nouvel
état suit K(sn,an,·). Si le joueur ne sélectionne plus rien, l'instant suivant
vaut +∞. Cette attente ne devient pas une transition probabiliste implicite.
Le noyau K décrit l'aléa du modèle ; une exécution avec sa graine déjà fixée
est déterministe, comme dans le moteur existant.

## 7. Deux niveaux d'étapes

Le moteur de jeu expose les commandes détaillées de combat. Le graphe d'aventure
regroupe un combat entier dans la résolution du choix qui l'a déclenché.

Le compteur k de la fairness existante compte les choix de scène résolus, combat
compris. Il ne compte ni les secondes, ni les images, ni les pressions de touches,
ni chaque point de manœuvre comme un nouveau tour d'aventure.

Une partie qui reste dans une scène sans sélectionner de choix ne progresse pas
dans ce compteur. Les limites de combat et les issues stalled/censored restent
celles du simulateur existant.

## 8. Joueur uniforme réservé aux tests

Pour une scène s, le test utilise :

    πU(a | s) = 1 / |A(s)|.

Dans un combat, le protocole actuel choisit uniformément une manœuvre, puis
uniformément une cible vivante si cette manœuvre en demande une.

L'affichage d'un point par couple manœuvre/cible ne change pas ce protocole.
Choisir uniformément tous les points de combat aplatirait ces deux choix et
donnerait une autre distribution ; le validateur ne le fait pas.

Un joueur humain choisit librement. Des touches tirées uniformément ne donnent
pas des choix d'arêtes uniformes et ne remplacent pas le protocole statistique.

## 9. Conservation des probabilités et de la fairness

En supprimant les déplacements et les animations d'une partie 3D, on obtient une
suite de commandes et d'états du moteur existant.

Sous le même protocole de choix et de dés, les distributions de ces suites
logiques sont les mêmes, sous réserve que les interactions sélectionnées soient
effectivement atteintes et que leur résolution termine.

La justification est une récurrence sur les transitions logiques : les états
initiaux projetés sont égaux ; les distributions de choix sont égales ; chaque
commande utilise le même noyau du moteur. Les lois des préfixes logiques sont donc
égales. Les durées de déplacement ne participent pas à cette récurrence.

Pour tout critère φ portant sur ces préfixes :

    P3D(φ après projection) = Pgraphe(φ).

Le contrat de fairness garde sa forme :

    Fair(G) ⇔ pour chaque critère j, Lj ≤ pj(G) ≤ Uj.

Le test statistique conserve ses simulations, ses conditions d'éligibilité et ses
intervalles de confiance. Il admet une aventure quand tous les intervalles sont
inclus dans leurs bandes. Le moteur 3D n'a pas à être lancé pendant ces simulations.

Cette conservation ne concerne pas une propriété exprimée en secondes physiques,
ni une nouvelle mécanique dépendant des positions. Le modèle ne remplace pas les
choix humains par une politique uniforme pendant une partie réelle.

## 10. Wish et initialisation

Un Wish suit le circuit existant : génération du brouillon, vérification des
règles, admission statistique, sauvegarde, puis chargement et début de partie.

La scène initiale du jeu admis fournit les premières commandes. Le navigateur
construit automatiquement leurs objets et points d'interaction. Chaque nouvelle vue reconstruit les
points à partir des commandes autorisées ; aucune géométrie écrite par le DM
n'est requise pour rendre les choix accessibles.

Les descriptions et les images contrôlées du Wish personnalisent les lieux.
Elles ne définissent pas les transitions. Une image absente ou refusée ne
supprime ni un point ni une possibilité de jeu.

## 11. Portée de la vérification

La physique et le moteur de rendu 3D ne sont pas formellement vérifiés.

- Lean reste l'autorité pour les commandes et les résultats. Ses théorèmes
  existants portent notamment sur les entrées permises et refusées.
- Le navigateur contrôle la correspondance des interactions aux entrées offertes.
- Des tests de navigation vérifient l'accessibilité de dispositions générées.
- Un test navigateur exécute un Wish enregistré, atteint des objets avec les
  touches, joue un combat et atteint un état terminal.

La conservation exposée au §9 est une propriété mathématique du contrat
d'interface. Elle n'est pas présentée comme une preuve Lean du navigateur,
de Three.js ou de la géométrie. Les contrôles et les tests fournissent les
éléments de validation de cette interface exécutée.

Les ajouts de règles en cours de partie sont réservés à un travail ultérieur.

## 12. Campagnes longues et affichage des combats

Le profil des nouveaux Wishes est désormais versionné : exploration-10-v1,
référence de Weibull de médiane discrète 10, admission sur 15 choix de scène.
Les anciens jeux conservent le profil legacy. Les mesures et leurs limites sont
décrites dans [le rapport de la campagne de Napoléon](napoleon-validation.md).
Cette modification de référence a été demandée par le joueur ; la projection
spatiale et la politique uniforme de test du §9 gardent le même sens.

Une réponse du moteur contient l'état final et une suite ordonnée de rapports.
Pendant sa lecture, l'interface présente le préfixe de ces rapports déjà affiché :
les HP et la scène visibles correspondent à ce préfixe. Elle bloque toute nouvelle
commande jusqu'à la fin de la lecture. Les boutons de combat et les touches
numériques transmettent exactement les mêmes entrées que les objets spatiaux.

Accélérer ou sauter l'animation modifie le temps d'affichage des rapports. Cela
ne modifie ni les faces des dés, ni leur ordre, ni l'état final fourni par Lean.
